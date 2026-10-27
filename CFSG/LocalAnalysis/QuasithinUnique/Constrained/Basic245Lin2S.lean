module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245Lin2Semilin
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.QuasithinUnique.Setup.Campbell CFSG.SL2MinimalFaithful
open scoped commutatorElement MatrixGroups LinearAlgebra.Projectivization

namespace C56

variable {G : Type} [Group G]

variable {L : Subgroup G} {F : Type} [Field F]

variable [Finite G]

section Kernel

open CFSG.QuasithinUnique.Setup.SL2Modules

theorem smul_eq_natEndHom (g : Matrix.SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    g • w = natEndHom F g w := by
  rw [natEndHom_apply, Matrix.SpecialLinearGroup.smul_def, Matrix.smul_eq_mulVec]

theorem phi_ker_mem [Finite F] [CharP F 2] (hL : IsShort2 L) (D : Lin2Data L F) {S T : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hTL : T ≤ L) (hTS : T ≤ S)
    (hTn : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T) {p : ℙ F (Fin 2 → F)}
    (hTp : ∀ l : ↥L, D.α l ∈ rootGrp p ↔ (l : G) ∈ T) (Ψ : ↥S →* AddMonoid.End (Fin 2 → F))
    (hΨ : ∀ (s : ↥S) (u v : ↥(blockU L)), (v : G) = (s : G) * u * (s : G)⁻¹ →
      Ψ s (Multiplicative.toAdd (D.β u)) = Multiplicative.toAdd (D.β v))
    (s : ↥S) (hlin : ∀ (c : F) (v : Fin 2 → F), Ψ s (c • v) = c • Ψ s v) :
    (s : G) ∈ T ⊔ (S ⊓ Subgroup.centralizer (blockU L : Set G)) := by
  classical
  have hfix : ∀ {t : Matrix.SpecialLinearGroup (Fin 2) F}, t ∈ rootGrp p →
      ∀ v ∈ p.submodule, t • v = v := by
    intro t ht v hv
    by_cases ht1 : t = 1
    · rw [ht1, one_smul]
    · exact (smul_eq_self_iff_mem_of_mem_rootGrp ht ht1 v).mpr hv
  obtain ⟨t₁, ht₁, ht₁1⟩ := exists_ne_one_mem_rootGrp (k := F) p
  have hp : ∀ v ∈ p.submodule, Ψ s v ∈ p.submodule := by
    intro v hv
    refine (smul_eq_self_iff_mem_of_mem_rootGrp ht₁ ht₁1 (Ψ s v)).mp ?_
    obtain ⟨b, hb⟩ := D.surj_α t₁
    have hbT : (b : G) ∈ T := (hTp b).mp (by rw [hb]; exact ht₁)
    have hb' : (s : G)⁻¹ * b * (s : G) ∈ T := by
      have := hTn _ (inv_mem s.2) _ hbT
      simpa using this
    let b' : ↥L := ⟨_, hTL hb'⟩
    have hconj := psi_conj D hSL Ψ hΨ s b' b (by
      show (b : G) = (s : G) * ((s : G)⁻¹ * b * (s : G)) * (s : G)⁻¹
      group) v
    rw [smul_eq_natEndHom, ← hb, ← hconj]
    have hα : D.α b' ∈ rootGrp p := (hTp b').mpr hb'
    rw [← smul_eq_natEndHom, hfix hα v hv]
  obtain ⟨m, hm⟩ := hS2 s
  have hΨm : ∀ v, (⇑(Ψ s))^[2 ^ m] v = v := by
    intro v
    have h1 : (Ψ s) ^ (2 ^ m) = 1 := by rw [← map_pow, hm, map_one]
    have h2 := congrArg (fun f : AddMonoid.End (Fin 2 → F) => f v) h1
    simpa [AddMonoid.End.coe_pow] using h2
  obtain ⟨t, ht, hgt₀⟩ := kl_linear p (Ψ s) hlin hp hΨm
  have hgt : ∀ v : Fin 2 → F, (Ψ s) v = t • v := fun v => hgt₀ v
  obtain ⟨b₀, hb₀⟩ := D.surj_α t
  have hb₀T : (b₀ : G) ∈ T := (hTp b₀).mp (by rw [hb₀]; exact ht)
  have hr'N : (b₀ : G)⁻¹ * (s : G) ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (inv_mem (Subgroup.le_normalizer b₀.2)) (hSL s.2)
  have htriv : ∀ (u : ↥(blockU L))
      (hu : (b₀ : G)⁻¹ * (s : G) * (u : G) * ((b₀ : G)⁻¹ * (s : G))⁻¹ ∈ blockU L),
      D.β ⟨(b₀ : G)⁻¹ * (s : G) * (u : G) * ((b₀ : G)⁻¹ * (s : G))⁻¹, hu⟩ = D.β u := by
    intro u hu
    have hsu : (s : G) * u * (s : G)⁻¹ ∈ blockU L :=
      (Subgroup.mem_normalizer_iff.mp (C1.mem_normalizer_blockU (hSL s.2)) u).mp u.2
    have h1 := hΨ s u ⟨_, hsu⟩ rfl
    have h2 := D.equiv_smul (b₀⁻¹) ⟨_, hsu⟩ ⟨_, hu⟩ (by
      show (b₀ : G)⁻¹ * (s : G) * (u : G) * ((b₀ : G)⁻¹ * (s : G))⁻¹ =
        (b₀ : G)⁻¹ * ((s : G) * u * (s : G)⁻¹) * ((b₀ : G)⁻¹)⁻¹
      group)
    apply Multiplicative.toAdd.injective
    show Multiplicative.toAdd (D.β ⟨_, hu⟩) = Multiplicative.toAdd (D.β u)
    rw [h2, ← h1, hgt, map_inv, hb₀, inv_smul_smul]
  have hcent := centralizes_of_trivial_quot hL D.α D.ker_α D.β D.surj_β D.ker_β D.equiv hr'N htriv
  have hr'S : (b₀ : G)⁻¹ * (s : G) ∈ S := mul_mem (inv_mem (hTS hb₀T)) s.2
  have hr'C : (b₀ : G)⁻¹ * (s : G) ∈ Subgroup.centralizer (blockU L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu => (hcent u hu).symm
  have hs : (s : G) = (b₀ : G) * ((b₀ : G)⁻¹ * (s : G)) := by group
  rw [hs]
  exact mul_mem (Subgroup.mem_sup_left hb₀T) (Subgroup.mem_sup_right ⟨hr'S, hr'C⟩)

end Kernel

open CFSG.QuasithinUnique.Setup.SL2Modules in
theorem lin2_S_facts {T S : Subgroup G} (hL : IsShort2 L) {n : ℕ} (hn : 1 ≤ n)
    (hlin : IsLin2Type L n) (hT : IsSylowTwoOf T L) (hS2 : IsPGroup 2 S)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) (hTS : T ≤ S)
    (hTn : ∀ s ∈ S, ∀ t ∈ T, s * t * s⁻¹ ∈ T) :
    (∀ E : Subgroup G, E ≤ S → (∀ e ∈ E, e * e = 1) →
      Nat.card E ≤ 2 * Nat.card ↥(E ⊓ (T ⊔ (S ⊓ Subgroup.centralizer (blockU L : Set G))))) ∧
    (∀ s ∈ S, (∀ w ∈ ⁅blockU L, T⁆, s * w = w * s) →
      s ∈ T ⊔ (S ⊓ Subgroup.centralizer (blockU L : Set G))) := by
  classical
  have hlin' := hlin
  obtain ⟨F, hFfield, hFfin, hcard, α, hαs, hαk, β, hβs, hβk, hβe⟩ := hlin'
  let D : Lin2Data L F := ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hq
  obtain ⟨p, -, hTp⟩ := lin2_exists_point hn hT hq D.α D.surj_α D.ker_α
  obtain ⟨Ψ, hΨ⟩ := exists_psi D hSL
  obtain ⟨Φ, hΦ⟩ := exists_phi D hSL Ψ hΨ
  have hTL : T ≤ L := hT.le
  have hkerΦ : ∀ s : ↥S, Φ s = 1 →
      (s : G) ∈ T ⊔ (S ⊓ Subgroup.centralizer (blockU L : Set G)) := by
    intro s hs
    refine phi_ker_mem hL D hS2 hSL hTL hTS hTn hTp Ψ hΨ s (fun c v => ?_)
    simp [hΦ, hs]
  refine ⟨?_, ?_⟩
  · intro E hES hE2
    let ΦE : ↥E →* RingAut F := Φ.comp (Subgroup.inclusion hES)
    have hrange : Nat.card ΦE.range ≤ 2 := by
      have hcyc : IsCyclic (RingAut F) :=
        (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two F hq).2
      have : IsCyclic ΦE.range := Subgroup.isCyclic _
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ΦE.range)
      have hg2 : g * g = 1 := by
        obtain ⟨e, he⟩ := g.2
        have hee : e * e = 1 := Subtype.ext (hE2 e e.2)
        apply Subtype.ext
        show (g : RingAut F) * (g : RingAut F) = 1
        rw [← he, ← map_mul, hee, map_one]
      have hord : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact Nat.le_of_dvd two_pos hord
    have hcardE : Nat.card ΦE.ker * Nat.card ΦE.range = Nat.card E :=
      Subgroup.card_ker_mul_card_range ΦE
    have hker_le : (ΦE.ker).map E.subtype ≤
        E ⊓ (T ⊔ (S ⊓ Subgroup.centralizer (blockU L : Set G))) := by
      rintro _ ⟨e, he, rfl⟩
      exact ⟨e.2, hkerΦ ⟨e, hES e.2⟩ he⟩
    have hkercard : Nat.card ΦE.ker ≤
        Nat.card ↥(E ⊓ (T ⊔ (S ⊓ Subgroup.centralizer (blockU L : Set G)))) := by
      calc Nat.card ΦE.ker = Nat.card ((ΦE.ker).map E.subtype) :=
            (Subgroup.card_map_of_injective E.subtype_injective).symm
        _ ≤ _ := Subgroup.card_le_of_le hker_le
    calc Nat.card E = Nat.card ΦE.ker * Nat.card ΦE.range := hcardE.symm
      _ ≤ Nat.card ↥(E ⊓ (T ⊔ (S ⊓ Subgroup.centralizer (blockU L : Set G)))) * 2 :=
          Nat.mul_le_mul hkercard hrange
      _ = _ := mul_comm _ _
  · intro s hs hcentr
    refine hkerΦ ⟨s, hs⟩ ?_
    obtain ⟨t₁, ht₁, ht₁1⟩ := exists_ne_one_mem_rootGrp (k := F) p
    obtain ⟨b₁, hb₁⟩ := D.surj_α t₁
    have hb₁T : (b₁ : G) ∈ T := (hTp b₁).mp (by rw [hb₁]; exact ht₁)
    have hfixed : ∀ v ∈ p.submodule, Ψ ⟨s, hs⟩ v = v := by
      intro v hv
      obtain ⟨w, hw⟩ := exists_smul_sub_eq ht₁ ht₁1 hv
      obtain ⟨u', hu'⟩ := D.surj_β (Multiplicative.ofAdd w)
      have hu'w : Multiplicative.toAdd (D.β u') = w := by rw [hu']; rfl
      have hcU : (b₁ : G) * u' * (b₁ : G)⁻¹ ∈ blockU L :=
        (Subgroup.mem_normalizer_iff.mp (C1.le_normalizer_blockU L b₁.2) u').mp u'.2
      obtain ⟨c, hcdef⟩ : ∃ c : ↥(blockU L), (c : G) = (b₁ : G) * u' * (b₁ : G)⁻¹ :=
        ⟨⟨_, hcU⟩, rfl⟩
      have hβc := D.equiv_smul b₁ u' c hcdef
      have hβu : Multiplicative.toAdd (D.β (c * u'⁻¹)) = v := by
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hβc, hu'w, hb₁, ← hw, sub_eq_add_neg]
      have huG : ((c * u'⁻¹ : ↥(blockU L)) : G) = ⁅(b₁ : G), (u' : G)⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hcdef, commutatorElement_def]
      have huC : ((c * u'⁻¹ : ↥(blockU L)) : G) ∈ ⁅blockU L, T⁆ := by
        rw [huG, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hb₁T u'.2
      have hcomm := hcentr _ huC
      have hconj : ((c * u'⁻¹ : ↥(blockU L)) : G) =
          s * ((c * u'⁻¹ : ↥(blockU L)) : G) * s⁻¹ := by
        rw [hcomm]; group
      have := hΨ ⟨s, hs⟩ (c * u'⁻¹) (c * u'⁻¹) hconj
      rw [hβu] at this
      exact this
    ext c
    have hv₀ : p.rep ∈ p.submodule := by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _
    have hcv₀ : c • p.rep ∈ p.submodule := p.submodule.smul_mem c hv₀
    have h1 := hfixed _ hcv₀
    rw [hΦ, hfixed _ hv₀] at h1
    have h2 : (Φ ⟨s, hs⟩ c - c) • p.rep = 0 := by rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h p.rep_nonzero

end C56

end CFSG.QuasithinUnique
