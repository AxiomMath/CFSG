module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups

public section

namespace CFSG.AGLEmbedding.LeviBlock

theorem le_ker_or_map_eq_alternatingGroup {X : Type*} [Group X] [Finite X] {n : ℕ}
    (ρ : X →* Equiv.Perm (Fin n)) (hρ : Function.Surjective ρ) {O W : Subgroup X} [O.Normal]
    (hO3 : Nat.Coprime 3 (Nat.card O)) [(W ⊔ O).Normal] (hW : ⁅W, W⁆ = W) :
    W ≤ ρ.ker ∨ (5 ≤ n ∧ W.map ρ = alternatingGroup (Fin n)) := by
  classical
  set A := alternatingGroup (Fin n) with hA
  have hWA : W.map ρ ≤ A := by
    have hc : ⁅W.map ρ, W.map ρ⁆ = W.map ρ := by rw [← Subgroup.map_commutator, hW]
    rw [← hc, hA, alternatingGroup_eq_sign_ker]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (Abelianization.commutator_subset_ker Equiv.Perm.sign)
  by_cases hn : 5 ≤ n
  · have h5 : 5 ≤ Nat.card (Fin n) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn
    have : IsSimpleGroup A := alternatingGroup.isSimpleGroup h5
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    have h3A : 3 ∣ Nat.card A := by
      have hAc := two_mul_nat_card_alternatingGroup (α := Fin n)
      rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hAc
      have h3 : 3 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
      rw [← hAc] at h3
      exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3
    set N := O.map ρ with hNdef
    have hN : N.Normal := ‹O.Normal›.map ρ hρ
    have hM : (W.map ρ ⊔ N).Normal := by
      rw [← Subgroup.map_sup]
      exact ‹(W ⊔ O).Normal›.map ρ hρ
    by_cases hMbot : W.map ρ ⊔ N = ⊥
    · left
      refine (Subgroup.map_eq_bot_iff W).mp (le_bot_iff.mp ?_)
      exact hMbot ▸ le_sup_left
    · right
      refine ⟨hn, le_antisymm hWA ?_⟩
      have hntM : Nontrivial ↥(W.map ρ ⊔ N) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hMbot
      have hAM : A ≤ W.map ρ ⊔ N :=
        Equiv.Perm.alternatingGroup_le_of_normal (α := Fin n) h5 hntM
      have hNA : ∀ x ∈ N, x ∈ A → x = 1 := by
        have hNs : (N.subgroupOf A).Normal := Subgroup.Normal.subgroupOf hN A
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf A) with h | h
        · intro x hxN hxA
          have hx : (⟨x, hxA⟩ : A) ∈ N.subgroupOf A := Subgroup.mem_subgroupOf.mpr hxN
          rw [h, Subgroup.mem_bot] at hx
          exact congrArg Subtype.val hx
        · exfalso
          have hAN : A ≤ N := fun a ha => by
            have ha' : (⟨a, ha⟩ : A) ∈ N.subgroupOf A := h ▸ Subgroup.mem_top _
            exact Subgroup.mem_subgroupOf.mp ha'
          have hd : Nat.card A ∣ Nat.card O :=
            (Subgroup.card_dvd_of_le hAN).trans (Subgroup.card_map_dvd O ρ)
          exact absurd (Nat.Coprime.coprime_dvd_right (h3A.trans hd) hO3) (by norm_num)
      intro a ha
      obtain ⟨w, hw, m, hm, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (hAM ha)
      have hmA : m ∈ A := by
        have := A.mul_mem (A.inv_mem (hWA hw)) ha
        rwa [inv_mul_cancel_left] at this
      rw [hNA m hm hmA, mul_one]
      exact hw
  · left
    have hsolA : Group.IsSolvable A :=
      alternatingGroup.isSolvable (α := Fin n)
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    have hbot : W.map ρ = ⊥ := by
      by_contra hne
      have hnt : Nontrivial ↥(W.map ρ) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
      have : Group.IsPerfect ↥W := Subgroup.isPerfect_iff.mpr hW
      let σ₀ : ↥W →* ↥(W.map ρ) := (ρ.comp W.subtype).codRestrict (W.map ρ)
        (fun w => ⟨w, w.2, rfl⟩)
      have hσ₀ : Function.Surjective σ₀ := by
        rintro ⟨a, ha⟩
        obtain ⟨w, hw, rfl⟩ := ha
        exact ⟨⟨w, hw⟩, rfl⟩
      have hperf : Group.IsPerfect ↥(W.map ρ) :=
        Group.IsPerfect.ofSurjective (f := σ₀) hσ₀
      let f : ↥(W.map ρ) →* A :=
        { toFun := fun x => ⟨x.1, hWA x.2⟩
          map_one' := by ext; rfl
          map_mul' := fun a b => by ext; rfl }
      have hf : Function.Injective f := fun a b h =>
        Subtype.ext (congrArg (fun y : ↥A => (y : Equiv.Perm (Fin n))) h)
      have : Group.IsSolvable ↥A := hsolA
      have hsol : Group.IsSolvable ↥(W.map ρ) :=
        Group.isSolvable_of_isSolvable_injective (f := f) hf
      exact (Group.IsPerfect.not_isSolvable (G := ↥(W.map ρ))) hsol
    exact (Subgroup.map_eq_bot_iff W).mp hbot

theorem map_ker_eq_top_or_card_eq {W T U : Type*} [Group W] [Group T] [Group U]
    [IsSimpleGroup T] [IsSimpleGroup U] (σ : W →* T) (hσ : Function.Surjective σ) (ψ : W →* U)
    (hψ : Function.Surjective ψ) : σ.ker.map ψ = ⊤ ∨ Nat.card T = Nat.card U := by
  have : (σ.ker.map ψ).Normal := (MonoidHom.normal_ker σ).map ψ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (σ.ker.map ψ) with h | h
  · right
    obtain ⟨φ, hφ, -⟩ := exists_factor σ hσ ψ hψ ((Subgroup.map_eq_bot_iff _).mp h)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ.ker with hk | hk
    · exact Nat.card_congr (Equiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).mp hk, hφ⟩)
    · exfalso
      obtain ⟨a, b, hab⟩ := (IsSimpleGroup.toNontrivial (G := U)).exists_pair_ne
      obtain ⟨x, rfl⟩ := hφ a
      obtain ⟨y, rfl⟩ := hφ b
      have hx : x ∈ φ.ker := hk ▸ Subgroup.mem_top x
      have hy : y ∈ φ.ker := hk ▸ Subgroup.mem_top y
      exact hab (by rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy])
  · exact Or.inl h

theorem map_inf_eq_top {W U : Type*} [Group W] [Group U] [Group.IsPerfect W] (ψ : W →* U)
    (hψ : Function.Surjective ψ) {K₁ K₂ : Subgroup W} [K₁.Normal] [K₂.Normal]
    (h₁ : K₁.map ψ = ⊤) (h₂ : K₂.map ψ = ⊤) : (K₁ ⊓ K₂).map ψ = ⊤ := by
  have hU : ⁅(⊤ : Subgroup U), (⊤ : Subgroup U)⁆ = ⊤ := by
    have h := Subgroup.map_commutator (⊤ : Subgroup W) (⊤ : Subgroup W) ψ
    rw [← commutator_def, Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr hψ] at h
    exact h.symm
  refine eq_top_iff.mpr ?_
  calc (⊤ : Subgroup U) = ⁅K₁.map ψ, K₂.map ψ⁆ := by rw [h₁, h₂, hU]
    _ = ⁅K₁, K₂⁆.map ψ := (Subgroup.map_commutator _ _ _).symm
    _ ≤ (K₁ ⊓ K₂).map ψ := Subgroup.map_mono (Subgroup.commutator_le_inf K₁ K₂)

theorem card_dvd_ker_of_permProd_normal {X U : Type*} [Group X] [Finite X] [Group U]
    [IsSimpleGroup U] {r s : ℕ} (hrU : Nat.card (alternatingGroup (Fin r)) ≠ Nat.card U)
    (hsU : Nat.card (alternatingGroup (Fin s)) ≠ Nat.card U)
    (ρ : X →* Equiv.Perm (Fin r) × Equiv.Perm (Fin s)) (hρ : Function.Surjective ρ)
    {O W : Subgroup X} [O.Normal] (hO3 : Nat.Coprime 3 (Nat.card O)) [(W ⊔ O).Normal]
    (hW : ⁅W, W⁆ = W) (ψ : ↥W →* U) (hψ : Function.Surjective ψ) :
    Nat.card U ∣ Nat.card ρ.ker := by
  classical
  have : Group.IsPerfect ↥W := Subgroup.isPerfect_iff.mpr hW
  have key : ∀ {n : ℕ} (ρ' : X →* Equiv.Perm (Fin n)), Function.Surjective ρ' →
      Nat.card (alternatingGroup (Fin n)) ≠ Nat.card U → (ρ'.ker.subgroupOf W).map ψ = ⊤ := by
    intro n ρ' hρ' hnU
    rcases le_ker_or_map_eq_alternatingGroup ρ' hρ' hO3 hW with hle | ⟨hn, hWA⟩
    · rw [(Subgroup.subgroupOf_eq_top).mpr hle, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top.mpr hψ]
    · have h5 : 5 ≤ Nat.card (Fin n) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn
      have : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup h5
      let σ : ↥W →* alternatingGroup (Fin n) :=
        (ρ'.comp W.subtype).codRestrict (alternatingGroup (Fin n))
          (fun w => hWA ▸ ⟨w, w.2, rfl⟩)
      have hσ : Function.Surjective σ := by
        rintro ⟨a, ha⟩
        obtain ⟨w, hw, rfl⟩ := (hWA ▸ ha : a ∈ W.map ρ')
        exact ⟨⟨w, hw⟩, rfl⟩
      have hker : σ.ker = ρ'.ker.subgroupOf W := by
        ext w
        simp [σ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      rcases map_ker_eq_top_or_card_eq σ hσ ψ hψ with h | h
      · rwa [hker] at h
      · exact absurd h hnU
  let ρ₁ : X →* Equiv.Perm (Fin r) := (MonoidHom.fst _ _).comp ρ
  let ρ₂ : X →* Equiv.Perm (Fin s) := (MonoidHom.snd _ _).comp ρ
  have hρ₁ : Function.Surjective ρ₁ := Prod.fst_surjective.comp hρ
  have hρ₂ : Function.Surjective ρ₂ := Prod.snd_surjective.comp hρ
  have hker : ρ.ker = ρ₁.ker ⊓ ρ₂.ker := by
    ext x
    simp [ρ₁, ρ₂, MonoidHom.mem_ker, Prod.ext_iff]
  have : (ρ₁.ker.subgroupOf W).Normal := (MonoidHom.normal_ker ρ₁).subgroupOf W
  have : (ρ₂.ker.subgroupOf W).Normal := (MonoidHom.normal_ker ρ₂).subgroupOf W
  have hinf : (ρ.ker.subgroupOf W).map ψ = ⊤ := by
    have h : ρ.ker.subgroupOf W = ρ₁.ker.subgroupOf W ⊓ ρ₂.ker.subgroupOf W := by
      rw [hker]
      ext w
      simp [Subgroup.mem_subgroupOf]
    rw [h]
    exact map_inf_eq_top ψ hψ (key ρ₁ hρ₁ hrU) (key ρ₂ hρ₂ hsU)
  have h1 : Nat.card U ∣ Nat.card (ρ.ker.subgroupOf W) := by
    have := Subgroup.card_map_dvd (ρ.ker.subgroupOf W) ψ
    rwa [hinf, Subgroup.card_top] at this
  have h2 : Nat.card (ρ.ker.subgroupOf W) ∣ Nat.card ρ.ker := by
    rw [← Subgroup.card_map_of_injective W.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  exact h1.trans h2

theorem false_of_permProd_quotient_of_normal_section {Y : Type} [Group Y] [Finite Y]
    {P W O : Subgroup Y} {U : Type} [Group U] [Finite U] [IsSimpleGroup U] {r s : ℕ}
    (hOP : O ≤ P) (hWP : W ≤ P) (hPO : P ≤ Subgroup.normalizer (O : Set Y))
    (hPWO : P ≤ Subgroup.normalizer ((W ⊔ O : Subgroup Y) : Set Y))
    (hOc : Nat.Coprime 3 (Nat.card O)) (hW : ⁅W, W⁆ = W)
    (e : (↥P ⧸ CFSG.pCore 2 ↥P) ≃* (Equiv.Perm (Fin r) × Equiv.Perm (Fin s)))
    (h3U : 3 ∣ Nat.card U) (hrU : Nat.card (alternatingGroup (Fin r)) ≠ Nat.card U)
    (hsU : Nat.card (alternatingGroup (Fin s)) ≠ Nat.card U)
    (ψ : ↥(W.subgroupOf P) →* U) (hψ : Function.Surjective ψ) : False := by
  classical
  let ρ : ↥P →* Equiv.Perm (Fin r) × Equiv.Perm (Fin s) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥P))
  have hρ : Function.Surjective ρ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hO3 : Nat.Coprime 3 (Nat.card (O.subgroupOf P)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOP).toEquiv]
    exact hOc
  have hW' : ⁅W.subgroupOf P, W.subgroupOf P⁆ = W.subgroupOf P := by
    have : Group.IsPerfect ↥W := Subgroup.isPerfect_iff.mpr hW
    exact Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hWP).symm.toMonoidHom) (MulEquiv.surjective _))
  have : (O.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPO
  have : (W.subgroupOf P ⊔ O.subgroupOf P).Normal := by
    rw [← Subgroup.subgroupOf_sup hWP hOP]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hPWO
  have h := card_dvd_ker_of_permProd_normal (X := ↥P) hrU hsU ρ hρ (O := O.subgroupOf P)
    (W := W.subgroupOf P) hO3 hW' ψ hψ
  have hle : ρ.ker ≤ CFSG.pCore 2 ↥P := by
    intro x hx
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥P)]
    exact e.injective (hx.trans (e.map_one).symm)
  have hUk : Nat.card U ∣ Nat.card (CFSG.pCore 2 ↥P) :=
    h.trans (Subgroup.card_dvd_of_le hle)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥P))
  rw [hm] at hUk
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) (h3U.trans hUk)) (by norm_num)

end CFSG.AGLEmbedding.LeviBlock
