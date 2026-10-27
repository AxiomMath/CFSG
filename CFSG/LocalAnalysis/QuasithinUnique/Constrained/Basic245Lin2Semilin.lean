module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245NaturalLin2

public section

namespace CFSG.QuasithinUnique

open CFSG.QuasithinUnique.Setup.Campbell CFSG.SL2MinimalFaithful
open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

namespace C56

section Plane

variable {F : Type} [Field F]

theorem kl_linear [Finite F] [CharP F 2] (p : ℙ F (Fin 2 → F))
    (g : (Fin 2 → F) →+ (Fin 2 → F)) (hlin : ∀ (c : F) (v : Fin 2 → F), g (c • v) = c • g v)
    (hp : ∀ v ∈ p.submodule, g v ∈ p.submodule) {m : ℕ} (hm : ∀ v, g^[2 ^ m] v = v) :
    ∃ t ∈ rootGrp p, ∀ v : Fin 2 → F, g v = t • v := by
  obtain ⟨x, hx⟩ := exists_smul_pt0 (k := F) p
  let g₀ : (Fin 2 → F) →+ (Fin 2 → F) :=
    (AddMonoidHom.mk' (fun v : Fin 2 → F => x⁻¹ • v) (fun a b => smul_add x⁻¹ a b)).comp
      (g.comp (AddMonoidHom.mk' (fun v : Fin 2 → F => x • v) (fun a b => smul_add x a b)))
  have hg₀ : ∀ v : Fin 2 → F, g₀ v = x⁻¹ • g (x • v) := fun v => rfl
  have hsub : ∀ v : Fin 2 → F, v ∈ (pt0 : ℙ F (Fin 2 → F)).submodule → x • v ∈ p.submodule := by
    intro v hv
    rw [← hx, PSL.smul_submodule]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hv
  have hsub' : ∀ w : Fin 2 → F, w ∈ p.submodule → x⁻¹ • w ∈ (pt0 : ℙ F (Fin 2 → F)).submodule := by
    intro w hw
    have h1 : w ∈ x • (pt0 : ℙ F (Fin 2 → F)).submodule := by
      rw [← PSL.smul_submodule, hx]; exact hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_smul_pointwise_iff_exists _ _ _ |>.mp h1
    simpa using hv
  have hlin₀ : ∀ (c : F) (v : Fin 2 → F), g₀ (c • v) = c • g₀ v := by
    intro c v
    rw [hg₀, hg₀, smul_comm x c v, hlin, smul_comm x⁻¹ c]
  have hit : ∀ (k : ℕ) (v : Fin 2 → F), g₀^[k] v = x⁻¹ • g^[k] (x • v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [Function.iterate_succ_apply', ih, hg₀, smul_inv_smul, Function.iterate_succ_apply']
  have hm₀ : ∀ v, g₀^[2 ^ m] v = v := by
    intro v
    rw [hit, hm, inv_smul_smul]
  have hdec : ∀ v : Fin 2 → F, v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
    intro v; ext i; fin_cases i <;> simp
  have hg₀v : ∀ v : Fin 2 → F, g₀ v = v 0 • g₀ ![1, 0] + v 1 • g₀ ![0, 1] := by
    intro v
    conv_lhs => rw [hdec v]
    rw [map_add, hlin₀, hlin₀]
  obtain ⟨a, ha⟩ : ∃ a, g₀ ![1, 0] 0 = a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, g₀ ![1, 0] 1 = c := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, g₀ ![0, 1] 0 = b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, g₀ ![0, 1] 1 = d := ⟨_, rfl⟩
  have hc0 : c = 0 := by
    have h1 : (![1, 0] : Fin 2 → F) ∈ (pt0 : ℙ F (Fin 2 → F)).submodule := by
      rw [mem_span_e0_iff]; simp
    have h2 := hsub' _ (hp _ (hsub _ h1))
    rw [mem_span_e0_iff] at h2
    rw [← hc]
    simpa [hg₀] using h2
  have hgv : ∀ v : Fin 2 → F, g₀ v = ![a * v 0 + b * v 1, d * v 1] := by
    intro v
    rw [hg₀v v]
    ext i
    fin_cases i
    · simp [ha, hb]
      ring
    · simp [hc, hd, hc0]
      ring
  have hit1 : ∀ (k : ℕ) (v : Fin 2 → F), g₀^[k] v 1 = d ^ k * v 1 := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih => intro v; rw [Function.iterate_succ_apply', hgv]; simp [ih, pow_succ]; ring
  have hit0 : ∀ k : ℕ, g₀^[k] ![1, 0] 0 = a ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', hgv]
      have h1 : g₀^[k] ![1, 0] 1 = 0 := by
        have := hit1 k ![1, 0]; simpa using this
      simp [ih, h1, pow_succ]
      ring
  have hpow : ∀ z : F, z ^ 2 ^ m = 1 → z = 1 := by
    intro z hz
    have h2 : (z - 1) ^ 2 ^ m = 0 := by
      rw [sub_pow_char_pow, one_pow, hz, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp h2)
  have ha1 : a = 1 := by
    apply hpow
    have := hit0 (2 ^ m)
    rw [hm₀] at this
    simpa using this.symm
  have hd1 : d = 1 := by
    apply hpow
    have := hit1 (2 ^ m) ![0, 1]
    rw [hm₀] at this
    simpa using this.symm
  obtain ⟨t, ht, hgt⟩ : ∃ t ∈ rootGrp p, ∀ v : Fin 2 → F, g v = t • v := by
    refine ⟨x * unipotent b * x⁻¹, ?_, fun v => ?_⟩
    · rw [← hx, mem_rootGrp_smul_iff]
      simpa [mul_assoc] using (show unipotent b ∈ rootGrp (pt0 : ℙ F (Fin 2 → F)) by
        rw [rootGrp_pt0]; exact ⟨Multiplicative.ofAdd b, rfl⟩)
    · have h1 : g v = x • g₀ (x⁻¹ • v) := by
        rw [hg₀, smul_inv_smul, smul_inv_smul]
      rw [h1, hgv, ha1, hd1]
      simp only [one_mul]
      rw [← smul_unipotent_vec, ← mul_smul, ← mul_smul]
  exact ⟨t, ht, hgt⟩

end Plane

section Trivial

open CFSG.Open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem centralizes_of_trivial_quot {L : Subgroup G} (hL : IsShort2 L) {F : Type} [Field F]
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 2) F) (hαk : α.ker = CFSG.pCore 2 ↥L)
    (β : ↥(blockU L) →* Multiplicative (Fin 2 → F))
    (hβs : Function.Surjective β) (hβk : β.ker = (blockZ L).subgroupOf (blockU L))
    (hβe : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {r' : G} (hr'N : r' ∈ Subgroup.normalizer (L : Set G))
    (htriv : ∀ (u : ↥(blockU L)) (hu : r' * (u : G) * r'⁻¹ ∈ blockU L),
      β ⟨r' * u * r'⁻¹, hu⟩ = β u) :
    ∀ u ∈ blockU L, r' * u = u * r' := by
  classical
  have hUab : ∀ a ∈ blockU L, ∀ c ∈ blockU L, a * c = c * a := (C1.elemAb2_blockU hL).1
  have hT1 : ∀ l : L, l ∈ α.ker ↔ (l : G) ∈ blockQ L := fun l => by
    rw [hαk]; exact (mem_blockQ_iff l).symm
  have hkerZ : ∀ u : blockU L, β u = 1 → (u : G) ∈ blockZ L := fun u hu => by
    have : u ∈ (blockZ L).subgroupOf (blockU L) := hβk ▸ hu
    exact this
  let cj : ↥L → ↥(blockU L) → ↥(blockU L) := fun l u =>
    ⟨(l : G) * u * (l : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L l.2) u).mp u.2⟩
  have hequiv : ∀ (l : L) (u : blockU L),
      Multiplicative.toAdd (β (cj l u)) = (α l) • Multiplicative.toAdd (β u) := by
    intro l u
    rw [Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]
    exact hβe l u (cj l u) (by simp [cj])
  let σ : Multiplicative (Fin 2 → F) → ↥(blockU L) := Function.surjInv hβs
  have hσ : ∀ w, β (σ w) = w := fun w => Function.surjInv_eq hβs w
  have hσt : ∀ w : Fin 2 → F, Multiplicative.toAdd (β (σ (Multiplicative.ofAdd w))) = w := by
    intro w; rw [hσ]; rfl
  have hr'U : r' ∈ Subgroup.normalizer (blockU L : Set G) := C1.mem_normalizer_blockU hr'N
  have hr'U' : ∀ u ∈ blockU L, r' * u * r'⁻¹ ∈ blockU L := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hr'U u).mp hu
  have hr'U'' : ∀ u ∈ blockU L, r'⁻¹ * u * r' ∈ blockU L := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hr'U) u).mp hu
    simpa using this
  let ρ' : ↥(blockU L) → ↥(blockU L) := fun u => ⟨r' * u * r'⁻¹, hr'U' u u.2⟩
  let ρ'' : ↥(blockU L) → ↥(blockU L) := fun u => ⟨r'⁻¹ * u * r', hr'U'' u u.2⟩
  have hρ'ρ'' : ∀ u, ρ' (ρ'' u) = u := fun u =>
    Subtype.ext (by show r' * (r'⁻¹ * u * r') * r'⁻¹ = u; group)
  have hβtriv : ∀ u : blockU L, β (ρ' u) = β u := fun u => htriv u (hr'U' u u.2)
  have hβtriv' : ∀ u : blockU L, β (ρ'' u) = β u := by
    intro u
    have := hβtriv (ρ'' u)
    rw [hρ'ρ''] at this
    exact this.symm
  have hαl' : ∀ (l : L) (hl' : r' * (l : G) * r'⁻¹ ∈ L),
      α ⟨r' * (l : G) * r'⁻¹, hl'⟩ = α l := by
    intro l hl'
    set l' : L := ⟨r' * (l : G) * r'⁻¹, hl'⟩ with hl'def
    have key : ∀ w : Fin 2 → F, (α l') • w = (α l) • w := by
      intro w
      set u := σ (Multiplicative.ofAdd w) with hu
      have e1 : Multiplicative.toAdd (β u) = w := hσt w
      have e2 : cj l' u = ρ' (cj l (ρ'' u)) := by
        apply Subtype.ext
        show (r' * (l : G) * r'⁻¹) * u * (r' * (l : G) * r'⁻¹)⁻¹ =
          r' * ((l : G) * (r'⁻¹ * u * r') * (l : G)⁻¹) * r'⁻¹
        group
      have h3 : Multiplicative.toAdd (β (cj l' u)) = (α l) • Multiplicative.toAdd (β u) := by
        rw [e2, hβtriv, hequiv, hβtriv']
      rw [← e1, ← hequiv l' u, h3]
    have h4 : (α l)⁻¹ * α l' = 1 :=
      sl2_eq_one_of_forall_smul_eq (fun w => by rw [mul_smul, key w, inv_smul_smul])
    exact (inv_mul_eq_one.mp h4).symm
  have hcjl : ∀ (l : L) (hl' : r' * (l : G) * r'⁻¹ ∈ L) (u : blockU L),
      cj ⟨r' * (l : G) * r'⁻¹, hl'⟩ u = cj l u := by
    intro l hl' u
    set l' : L := ⟨r' * (l : G) * r'⁻¹, hl'⟩ with hl'def
    have hker : l'⁻¹ * l ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hαl' l hl', inv_mul_cancel]
    have hq : ((l'⁻¹ * l : L) : G) ∈ blockQ L := (hT1 _).mp hker
    set qG : G := ((l'⁻¹ * l : L) : G) with hqG
    have hcomm' : qG * u * qG⁻¹ = u := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (C1.blockU_comm hL u u.2 qG hq).symm
    have hl_eq : (l : G) = (l' : G) * qG := by
      rw [hqG]; simp
    apply Subtype.ext
    show (l' : G) * u * (l' : G)⁻¹ = (l : G) * u * (l : G)⁻¹
    rw [hl_eq]
    calc (l' : G) * u * (l' : G)⁻¹ = (l' : G) * (qG * u * qG⁻¹) * (l' : G)⁻¹ := by rw [hcomm']
      _ = ((l' : G) * qG) * u * ((l' : G) * qG)⁻¹ := by group
  have hKU : blockU L ≤ blockU L ⊓ centralizer ({r'} : Set G) := by
    refine (C1.commutator_blockU hL).symm.le.trans ?_
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have hlU : l * u⁻¹ * l⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L hl) _).mp (inv_mem hu)
    have hcommU : ⁅u, l⁆ ∈ blockU L := by
      have := mul_mem hu hlU
      rw [commutatorElement_def]
      simpa [mul_assoc] using this
    refine ⟨hcommU, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    set lL : L := ⟨l, hl⟩ with hlL
    have hl' : r' * l * r'⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hr'N l).mp hl
    set u' : blockU L := ⟨u, hu⟩ with hu'
    set z₀ : blockU L := u'⁻¹ * ρ' u' with hz₀def
    have hz₀Z : (z₀ : G) ∈ blockZ L := hkerZ z₀ (by
      rw [hz₀def, map_mul, map_inv, hβtriv, inv_mul_cancel])
    have hz₀l : l * (z₀ : G) = (z₀ : G) * l := Subgroup.mem_centralizer_iff.mp hz₀Z.2 l hl
    have hu₂ : r' * u * r'⁻¹ = u * (z₀ : G) := by
      rw [hz₀def, Subgroup.coe_mul, Subgroup.coe_inv]
      show r' * u * r'⁻¹ = u * (u⁻¹ * (r' * u * r'⁻¹))
      group
    have hx : (r' * l * r'⁻¹) * (r' * u * r'⁻¹)⁻¹ * (r' * l * r'⁻¹)⁻¹ =
        l * (r' * u * r'⁻¹)⁻¹ * l⁻¹ := by
      have h1 := congrArg Subtype.val (hcjl lL hl' (ρ' u')⁻¹)
      simpa [cj, ρ', Subgroup.coe_inv] using h1
    have hfinal : r' * ⁅u, l⁆ * r'⁻¹ = ⁅u, l⁆ := by
      calc r' * ⁅u, l⁆ * r'⁻¹
          = (r' * u * r'⁻¹) * ((r' * l * r'⁻¹) * (r' * u * r'⁻¹)⁻¹ * (r' * l * r'⁻¹)⁻¹) := by
            rw [commutatorElement_def]; group
        _ = (r' * u * r'⁻¹) * (l * (r' * u * r'⁻¹)⁻¹ * l⁻¹) := by rw [hx]
        _ = (u * z₀) * (l * (u * z₀)⁻¹ * l⁻¹) := by rw [hu₂]
        _ = u * (z₀ * l * (z₀ : G)⁻¹) * u⁻¹ * l⁻¹ := by group
        _ = u * l * u⁻¹ * l⁻¹ := by
          have : (z₀ : G) * l * (z₀ : G)⁻¹ = l := by
            rw [← hz₀l]; group
          rw [this]
        _ = ⁅u, l⁆ := by rw [commutatorElement_def]
    calc r' * ⁅u, l⁆ = (r' * ⁅u, l⁆ * r'⁻¹) * r' := by group
      _ = ⁅u, l⁆ * r' := by rw [hfinal]
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp (hKU hu).2) r' rfl

end Trivial

end C56

end CFSG.QuasithinUnique
