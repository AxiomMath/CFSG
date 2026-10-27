module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParPres
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaParLType

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaPar

open Matrix Subgroup

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable {π : Γ →* (W →ₗ[ZMod 2] W)} {K : Subgroup Γ} {θ : K ≃* SU42b} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 8 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {B : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2}
  {τ : Γ →* Γ} {e : W ≃ₗ[ZMod 2] (Fin 16 → ZMod 2)} {z : ℕ}

@[expose] noncomputable def diagSU : SU42b →* SU42b × SU42b :=
  MonoidHom.prod (MonoidHom.id _) (MonoidHom.id _)

theorem uW_diag {z : ℕ} (hz : z = 0 ∨ z = 3) (s : Fin 3) : uXW z s = [s] ∧ uYW z s = [s] := by
  rcases hz with rfl | rfl <;> fin_cases s <;> decide

section Images


theorem wordSU_single (s : Fin 3) :
    (⟨wordGL [s], wordGL_mem _⟩ : SU42b) = genSU s := by
  apply Subtype.ext
  simp [wordGL, genSU]

theorem rhoMHom_genSU_eq (hz : z = 0 ∨ z = 3) (s : Fin 3) :
    rhoMHom (genSU s) = rhoU z (diagSU (genSU s)) := by
  have h := gens16M_eq_rhoU hz (k := s) (by omega)
  rw [(uW_diag hz s).1, (uW_diag hz s).2, wordSU_single, gens16M_lt3] at h
  have hd : diagSU (genSU s) = (genSU s, genSU s) := rfl
  rw [hd, ← h]
  simp [rhoMHom, genSU, coe_genGL]

theorem rhoM_eq_rhoU_diag (hz : z = 0 ∨ z = 3) (x : SU42b) : rhoMHom x = rhoU z (diagSU x) := by
  have key : rhoMHom = (rhoU z).comp diagSU := by
    refine MonoidHom.eq_of_eqOn_dense SU42b_eq_closure.symm ?_
    rintro x (rfl | rfl)
    · exact rhoMHom_genSU_eq hz 0
    · exact rhoMHom_genSU_eq hz 1
  exact DFunLike.congr_fun key x

theorem uTW_lt (z side s : ℕ) (hz : z = 0 ∨ z = 3) (hside : side < 2) (hs : s < 2) :
    ∀ l ∈ uTW z side s, l < 11 := by
  rcases hz with rfl | rfl <;> interval_cases side <;> interval_cases s <;> decide

theorem exists_rhoU_eq_matRep (hz : z = 0 ∨ z = 3) (hgen : K ⊔ D = ⊤)
    (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (hDe : ∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ) (γ : Γ) :
    ∃ p, rhoU z p = matRep π e γ := by
  let S : Subgroup Γ :=
    { carrier := {γ | ∃ p, rhoU z p = matRep π e γ}
      mul_mem' := by
        rintro a b ⟨g, hg⟩ ⟨g', hg'⟩
        exact ⟨g * g', by rw [map_mul, map_mul, hg, hg']⟩
      one_mem' := ⟨1, by rw [map_one, map_one]⟩
      inv_mem' := by
        rintro a ⟨g, hg⟩
        exact ⟨g⁻¹, (map_inv_eq_of_eq (matRep π e) (rhoU z) hg.symm).symm⟩ }
  have hpsi : ∀ ψ ∈ psiZ z, ∃ p, rhoU z p = 1 + embedM ψ := by
    intro ψ hψ
    refine Submodule.span_induction (p := fun ψ _ => ∃ p, rhoU z p = 1 + embedM ψ) ?_ ?_ ?_ ?_ hψ
    · rintro _ ⟨c, rfl⟩
      have h := gens16M_eq_rhoU hz (k := c + 3) (by omega)
      rw [gens16M_ge3 z (c + 3) (by omega) (by omega)] at h
      exact ⟨_, by rw [← h]; simp⟩
    · exact ⟨1, by rw [map_one, embedM_zero, add_zero]⟩
    · rintro x y _ _ ⟨g, hg⟩ ⟨g', hg'⟩
      exact ⟨g * g', by rw [map_mul, hg, hg', one_add_embedM_mul]⟩
    · intro a x _ hx
      rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a with rfl | rfl
      · exact ⟨1, by rw [map_one, zero_smul, embedM_zero, add_zero]⟩
      · rwa [one_smul]
  have hKS : K ≤ S := by
    intro k hk
    refine ⟨diagSU (θ ⟨k, hk⟩), ?_⟩
    rw [← rhoM_eq_rhoU_diag hz, matRep_apply, hK ⟨k, hk⟩]
    rfl
  have hDS : D ≤ S := by
    intro d hd
    obtain ⟨ψ, hψ, hdψ⟩ := hDe d hd
    obtain ⟨g, hg⟩ := hpsi ψ hψ
    exact ⟨g, by rw [hg, matRep_apply, hdψ]⟩
  have : S = ⊤ := eq_top_iff.mpr (hgen ▸ sup_le hKS hDS)
  exact (this ▸ Subgroup.mem_top γ : γ ∈ S)

theorem exists_matRep_eq_rhoU (hz : z = 0 ∨ z = 3)
    (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (hDe' : ∀ ψ ∈ psiZ z, ∃ d ∈ D, matOf e (π d) = 1 + embedM ψ) (p : SU42b × SU42b) :
    ∃ γ, matRep π e γ = rhoU z p := by
  have hword : ∀ w : List ℕ, (∀ l ∈ w, l < 11) → ∃ γ, matRep π e γ = (w.map (gens16M z)).prod := by
    intro w hw
    induction w with
    | nil => exact ⟨1, by rw [map_one]; rfl⟩
    | cons l w ih =>
      obtain ⟨γ, hγ⟩ := exists_matRep_eq_gens16M hK hDe' (hw l (by simp))
      obtain ⟨γ', hγ'⟩ := ih fun l' hl' => hw l' (by simp [hl'])
      exact ⟨γ * γ', by rw [map_mul, hγ, hγ', List.map_cons, List.prod_cons]⟩
  have hgen : ∀ s : Fin 3, s.val < 2 → (∃ γ, matRep π e γ = rhoU z (genSU s, 1)) ∧
      ∃ γ, matRep π e γ = rhoU z (1, genSU s) := by
    intro s hs
    obtain ⟨h0, h1⟩ := rhoU_eq_word hz hs
    rw [Fin.ofNat_val_eq_self] at h0 h1
    exact ⟨h0 ▸ hword _ (uTW_lt z 0 s hz (by norm_num) hs),
      h1 ▸ hword _ (uTW_lt z 1 s hz (by norm_num) hs)⟩
  have hp : p ∈ Subgroup.closure ((fun x => (x, (1 : SU42b))) '' {genSU 0, genSU 1} ∪
      (fun y => ((1 : SU42b), y)) '' {genSU 0, genSU 1}) := by
    rw [closure_inl_union_inr SU42b_eq_closure.symm SU42b_eq_closure.symm]
    exact Subgroup.mem_top p
  refine Subgroup.closure_induction (p := fun p _ => ∃ γ, matRep π e γ = rhoU z p) ?_ ?_ ?_ ?_ hp
  · rintro _ (⟨g, hg, rfl⟩ | ⟨g, hg, rfl⟩) <;> rcases hg with rfl | rfl
    exacts [(hgen 0 (by norm_num)).1, (hgen 1 (by norm_num)).1, (hgen 0 (by norm_num)).2,
      (hgen 1 (by norm_num)).2]
  · exact ⟨1, by rw [map_one, map_one]⟩
  · rintro x y _ _ ⟨γ, hγ⟩ ⟨γ', hγ'⟩
    exact ⟨γ * γ', by rw [map_mul, map_mul, hγ, hγ']⟩
  · rintro x _ ⟨γ, hγ⟩
    exact ⟨γ⁻¹, map_inv_eq_of_eq (matRep π e) (rhoU z) hγ⟩

end Images

section Main


theorem card_ker_subgroupOf {G : Type*} [Group G] {H N : Subgroup G} (hle : N ≤ H) :
    Nat.card (N.subgroupOf H) = Nat.card N :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

theorem exists_section_inl (lam : Γ →* SU42b × SU42b) (hsurj : Function.Surjective lam)
    (hZc : lam.ker ≤ center Γ) (hZo : Odd (Nat.card lam.ker)) :
    ∃ ψ : SU42b →* Γ, lam.comp ψ = MonoidHom.inl SU42b SU42b := by
  set Γ₁ := ((MonoidHom.snd SU42b SU42b).comp lam).ker
  set f₁ : Γ₁ →* SU42b := ((MonoidHom.fst SU42b SU42b).comp lam).comp Γ₁.subtype
  have hle : lam.ker ≤ Γ₁ := fun γ hγ => by
    rw [MonoidHom.mem_ker] at hγ ⊢; rw [MonoidHom.comp_apply, hγ]; rfl
  have hker : f₁.ker = lam.ker.subgroupOf Γ₁ := by
    ext ⟨γ, hγ⟩
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker]
    have hγ' : (lam γ).2 = 1 := hγ
    constructor
    · intro h1; exact Prod.ext h1 hγ'
    · intro h1; exact congrArg Prod.fst h1
  have hf₁ : Function.Surjective f₁ := by
    intro x
    obtain ⟨γ, hγ⟩ := hsurj (x, 1)
    refine ⟨⟨γ, ?_⟩, ?_⟩
    · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hγ]; rfl
    · change (lam γ).1 = x; rw [hγ]
  have hZc₁ : f₁.ker ≤ center Γ₁ := by
    rw [hker]
    rintro ⟨γ, hγ⟩ hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hZc hk) g)
  have hZo₁ : Odd (Nat.card f₁.ker) := by rw [hker, card_ker_subgroupOf hle]; exact hZo
  obtain ⟨ψ', hψ'⟩ := exists_section_SU42b f₁ hf₁ hZc₁ hZo₁
  refine ⟨Γ₁.subtype.comp ψ', ?_⟩
  ext1 x
  apply Prod.ext
  · exact DFunLike.congr_fun hψ' x
  · exact (ψ' x).2

theorem exists_section_inr (lam : Γ →* SU42b × SU42b) (hsurj : Function.Surjective lam)
    (hZc : lam.ker ≤ center Γ) (hZo : Odd (Nat.card lam.ker)) :
    ∃ ψ : SU42b →* Γ, lam.comp ψ = MonoidHom.inr SU42b SU42b := by
  set sw := (MulEquiv.prodComm (M := SU42b) (N := SU42b)).toMonoidHom
  have hsw : ∀ p, sw (sw p) = p := fun p => rfl
  have hker : (sw.comp lam).ker = lam.ker := by
    ext γ
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply]
    constructor
    · intro h1; rw [← hsw (lam γ), h1, map_one]
    · intro h1; rw [h1, map_one]
  obtain ⟨ψ, hψ⟩ := exists_section_inl (sw.comp lam)
    (fun p => by obtain ⟨γ, hγ⟩ := hsurj (sw p); exact ⟨γ, by simp [hγ, hsw]⟩)
    (hker ▸ hZc) (hker ▸ hZo)
  refine ⟨ψ, ?_⟩
  ext1 x
  have := DFunLike.congr_fun hψ x
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply] at this
  rw [MonoidHom.comp_apply, MonoidHom.inr_apply, ← hsw (lam (ψ x)), this]
  rfl

theorem closure_tSU : Subgroup.closure (Set.range fun a : Fin 5 => tSU a) = ⊤ := by
  rw [eq_top_iff, ← MonoidHom.range_eq_top.mpr presHom_surjective, MonoidHom.range_eq_map,
    ← PresentedGroup.closure_range_of, MonoidHom.map_closure, ← Set.range_comp]
  refine le_of_eq (congrArg Subgroup.closure ?_)
  ext x
  simp [presHom_of]

theorem R3Hyp.exists_equiv_SU42b_prod [Finite Γ] (h : R3Hyp π K θ τW ι D B τ)
    (he : matOf e τW = tM16) (hz : z = 0 ∨ z = 3)
    (hK : ∀ k : K, matOf e (π k) = rhoM ((θ k : GL (Fin 8) (ZMod 2)) : Mat8))
    (hDe : ∀ d ∈ D, ∃ ψ ∈ psiZ z, matOf e (π d) = 1 + embedM ψ)
    (hDe' : ∀ ψ ∈ psiZ z, ∃ d ∈ D, matOf e (π d) = 1 + embedM ψ) :
    ∃ ψ : SU42b × SU42b ≃* Γ, (∀ p, matOf e (π (ψ p)) = rhoU z p) ∧
      ∀ p, τ (ψ p) = ψ p.swap := by
  have hz4 : z < 4 := by rcases hz with rfl | rfl <;> norm_num
  have hF := exists_rhoU_eq_matRep (K := K) (θ := θ) (D := D) hz h.gen hK hDe
  set lam := factorHom (matRep π e) (rhoU z) (rhoU_injective z) hF with hlam
  have hsurj : Function.Surjective lam :=
    factorHom_surjective _ _ _ hF (exists_matRep_eq_rhoU hz hK hDe')
  have hker : lam.ker = π.ker := (factorHom_ker _ _ _ hF).trans (matRep_ker π e)
  have hZc : lam.ker ≤ center Γ := hker ▸ h.ker_le_center he hz4 hK hDe hDe'
  have hZo : Odd (Nat.card lam.ker) := hker ▸ h.odd_card_ker he
  obtain ⟨ψ₁, hψ₁⟩ := exists_section_inl lam hsurj hZc hZo
  obtain ⟨ψ₂, hψ₂⟩ := exists_section_inr lam hsurj hZc hZo
  have hl₁ : ∀ x, lam (ψ₁ x) = (x, 1) := fun x => DFunLike.congr_fun hψ₁ x
  have hl₂ : ∀ y, lam (ψ₂ y) = (1, y) := fun y => DFunLike.congr_fun hψ₂ y
  have hinvol : ∀ a : Fin 5, tSU a * tSU a = 1 := fun a => tSU_mul_self a.isLt
  have hc0 : ∀ a b : Fin 5, Commute (ψ₁ (tSU a)) (ψ₂ (tSU b)) := by
    intro a b
    refine commute_of_isTwoElt hZc hZo (isTwoElt_of_sq (by rw [← map_mul, hinvol, map_one]))
      (isTwoElt_of_sq (by rw [← map_mul, hinvol, map_one])) ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hl₁, hl₂, commutatorElement_def]
    simp
  have hc1 : ∀ x : SU42b, ∀ b : Fin 5, Commute (ψ₁ x) (ψ₂ (tSU b)) := by
    intro x b
    have hx : x ∈ Subgroup.closure (Set.range fun a : Fin 5 => tSU a) :=
      closure_tSU ▸ Subgroup.mem_top x
    refine Subgroup.closure_induction (p := fun x _ => Commute (ψ₁ x) (ψ₂ (tSU b))) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, rfl⟩; exact hc0 a b
    · rw [map_one]; exact Commute.one_left _
    · intro x y _ _ hx hy; rw [map_mul]; exact hx.mul_left hy
    · intro x _ hx; rw [map_inv]; exact hx.inv_left
  have hcomm : ∀ x y : SU42b, Commute (ψ₁ x) (ψ₂ y) := by
    intro x y
    have hy : y ∈ Subgroup.closure (Set.range fun a : Fin 5 => tSU a) :=
      closure_tSU ▸ Subgroup.mem_top y
    refine Subgroup.closure_induction (p := fun y _ => Commute (ψ₁ x) (ψ₂ y)) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨b, rfl⟩; exact hc1 x b
    · rw [map_one]; exact Commute.one_right _
    · intro y y' _ _ hy hy'; rw [map_mul]; exact hy.mul_right hy'
    · intro y _ hy; rw [map_inv]; exact hy.inv_right
  set ψ := MonoidHom.noncommCoprod ψ₁ ψ₂ hcomm
  have hψ : lam.comp ψ = MonoidHom.id (SU42b × SU42b) := by
    ext1 ⟨x, y⟩
    simp only [MonoidHom.comp_apply, ψ, MonoidHom.noncommCoprod_apply, map_mul, hl₁, hl₂,
      MonoidHom.id_apply, Prod.mk_mul_mk, mul_one, one_mul]
  have hlp : ∀ p, lam (ψ p) = p := fun p => DFunLike.congr_fun hψ p
  have hinj : Function.Injective ψ := fun p q hpq => by rw [← hlp p, hpq, hlp]
  have hnorm := range_normal_of_section lam ψ hψ hZc
  have hinv : ∀ γ, γ * γ = 1 → γ ∈ ψ.range := fun γ hγ =>
    mem_range_of_mul_self_eq_one lam ψ hψ hZc hZo hγ
  have hDr : D ≤ ψ.range := fun d hd => hinv d (h.D_mul_self hDe hd)
  have hKr : K ≤ ψ.range := K_le_of_normal ψ.range fun m hm => hDr (h.E_le m hm)
  have htop : ψ.range = ⊤ := eq_top_iff.mpr (h.gen ▸ sup_le hKr hDr)
  have hsurjψ : Function.Surjective ψ := MonoidHom.range_eq_top.mp htop
  refine ⟨MulEquiv.ofBijective ψ ⟨hinj, hsurjψ⟩, fun p => ?_, fun p => ?_⟩
  · show matOf e (π (ψ p)) = rhoU z p
    rw [← matRep_apply, ← factorHom_spec (matRep π e) (rhoU z) (rhoU_injective z) hF, ← hlam, hlp]
  · show τ (ψ p) = ψ p.swap
    have hτ : lam (τ (ψ p)) = p.swap := by
      apply rhoU_injective z
      rw [hlam, factorHom_spec, matRep_apply, matOf_π_τ h he, ← matRep_apply, ← factorHom_spec
        (matRep π e) (rhoU z) (rhoU_injective z) hF, ← hlam, hlp, tM16_rhoU hz]
    obtain ⟨q, hq⟩ := hsurjψ (τ (ψ p))
    rw [← hq, hlp] at hτ
    rw [← hq, hτ]

end Main

end CFSG.EvenSmallLie.UnitarySix.YamadaPar
