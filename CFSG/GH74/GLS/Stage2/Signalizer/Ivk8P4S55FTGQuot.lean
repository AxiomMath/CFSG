module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace FTG

open Subgroup CFSG CFSG.LocalCores

variable {D A B : Type*} [Group D] [Group A] [Group B]

theorem not_comm_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  have : Nontrivial Q := isQuasisimple_nontrivial hQ
  have : Group.IsPerfect Q := hQ.1
  exact Group.IsPerfect.not_isSolvable Q

theorem not_odd_card_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) :
    ¬ Odd (Nat.card Q) := fun h =>
  not_isSolvable_of_isQuasisimple hQ (CFSG.FeitThompson.isSolvable_of_odd_natCard _ h)

theorem ker_comp_mk' (φ : D →* A) (N : Subgroup A) [N.Normal] :
    ((QuotientGroup.mk' N).comp φ).ker = N.comap φ := by
  ext x
  simp [QuotientGroup.eq_one_iff]

variable [Finite D] {φ : D →* A} {ψ : D →* B}

theorem map_ker_le_center (hψ : Function.Surjective ψ) (hB : IsQuasisimple B)
    (hodd : Odd (Nat.card φ.ker)) : φ.ker.map ψ ≤ center B := by
  have hn : (φ.ker.map ψ).Normal := (MonoidHom.normal_ker φ).map ψ hψ
  rcases quasisimple_normal_subgroups hB hn with h | h
  · exfalso
    have : Finite B := Finite.of_surjective ψ hψ
    have hdvd : Nat.card ↥(φ.ker.map ψ) ∣ Nat.card φ.ker := Subgroup.card_map_dvd _ _
    rw [h, Subgroup.card_top] at hdvd
    exact not_odd_card_of_isQuasisimple hB (Odd.of_dvd_nat hodd hdvd)
  · exact h

theorem comap_center_eq (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
    (hA : IsQuasisimple A) (hB : IsQuasisimple B) (hodd : Odd (Nat.card φ.ker)) :
    (center A).comap φ = (center B).comap ψ := by
  have h1 : φ.ker ≤ (center B).comap ψ :=
    Subgroup.map_le_iff_le_comap.mp (map_ker_le_center hψ hB hodd)
  have h2 : (center B).comap ψ ≤ (center A).comap φ := by
    have hn : (((center B).comap ψ).map φ).Normal :=
      (inferInstance : ((center B).comap ψ).Normal).map φ hφ
    rcases quasisimple_normal_subgroups hA hn with h | h
    · exfalso
      have htop : (center B).comap ψ = ⊤ := by
        rw [eq_top_iff]
        intro d _
        have hd : φ d ∈ ((center B).comap ψ).map φ := by rw [h]; trivial
        obtain ⟨m, hm, hmd⟩ := hd
        have hk : m⁻¹ * d ∈ φ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hmd, inv_mul_cancel]
        have := mul_mem hm (h1 hk)
        rwa [mul_inv_cancel_left] at this
      obtain ⟨a, b, hab⟩ := not_comm_of_isQuasisimple hB
      obtain ⟨x, rfl⟩ := hψ a
      obtain ⟨y, rfl⟩ := hψ b
      have hx : ψ x ∈ center B := by
        have : x ∈ (center B).comap ψ := by rw [htop]; trivial
        exact this
      exact hab (Subgroup.mem_center_iff.mp hx (ψ y)).symm
    · exact Subgroup.map_le_iff_le_comap.mp h
  refine le_antisymm ?_ h2
  let fB : D →* B ⧸ center B := (QuotientGroup.mk' (center B)).comp ψ
  have hfB : Function.Surjective fB := (QuotientGroup.mk'_surjective _).comp hψ
  have hs : IsSimpleGroup (B ⧸ center B) := hB.2.1
  have hn : (((center A).comap φ).map fB).Normal :=
    (inferInstance : ((center A).comap φ).Normal).map fB hfB
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (((center A).comap φ).map fB) with h | h
  · intro d hd
    have : fB d ∈ ((center A).comap φ).map fB := ⟨d, hd, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    show ψ d ∈ center B
    exact (QuotientGroup.eq_one_iff (ψ d)).mp this
  · exfalso
    have htop : (center A).comap φ = ⊤ := by
      rw [eq_top_iff]
      intro d _
      have hd : fB d ∈ ((center A).comap φ).map fB := by rw [h]; trivial
      obtain ⟨m, hm, hmd⟩ := hd
      have hk : m⁻¹ * d ∈ (center B).comap ψ := by
        show ψ (m⁻¹ * d) ∈ center B
        rw [← QuotientGroup.eq_one_iff]
        change fB (m⁻¹ * d) = 1
        rw [map_mul, map_inv, hmd, inv_mul_cancel]
      have := mul_mem hm (h2 hk)
      rwa [mul_inv_cancel_left] at this
    obtain ⟨a, b, hab⟩ := not_comm_of_isQuasisimple hA
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    have hx : φ x ∈ center A := by
      have : x ∈ (center A).comap φ := by rw [htop]; trivial
      exact this
    exact hab (Subgroup.mem_center_iff.mp hx (φ y)).symm

@[expose] noncomputable def centerQuotEquiv (hφ : Function.Surjective φ)
    (hψ : Function.Surjective ψ) (hA : IsQuasisimple A) (hB : IsQuasisimple B)
    (hodd : Odd (Nat.card φ.ker)) : (A ⧸ center A) ≃* (B ⧸ center B) :=
  (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (center A)).comp φ)
      ((QuotientGroup.mk'_surjective _).comp hφ)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (by
        rw [ker_comp_mk', ker_comp_mk', comap_center_eq hφ hψ hA hB hodd])).trans
      (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (center B)).comp ψ)
        ((QuotientGroup.mk'_surjective _).comp hψ)))

theorem centerQuotEquiv_mk (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
    (hA : IsQuasisimple A) (hB : IsQuasisimple B) (hodd : Odd (Nat.card φ.ker)) (d : D) :
    centerQuotEquiv hφ hψ hA hB hodd (QuotientGroup.mk (φ d)) = QuotientGroup.mk (ψ d) := by
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (center A)).comp φ)
      ((QuotientGroup.mk'_surjective _).comp hφ)).symm
      (QuotientGroup.mk (φ d)) = QuotientGroup.mk d := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [centerQuotEquiv, MulEquiv.trans_apply]
  rw [h1]
  rfl

omit [Finite D] in
theorem card_comap_center (hψ : Function.Surjective ψ) :
    Nat.card ↥((center B).comap ψ) = Nat.card (center B) * Nat.card ψ.ker := by
  let M := (center B).comap ψ
  let f : ↥M →* ↥(center B) :=
    { toFun := fun m => ⟨ψ m, m.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hf : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨d, rfl⟩ := hψ b
    exact ⟨⟨d, hb⟩, rfl⟩
  have hker : f.ker = ψ.ker.subgroupOf M := by
    ext m
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have := congrArg Subtype.val h
      exact this
    · intro h
      exact Subtype.ext h
  have hle : ψ.ker ≤ M := fun d hd => by
    show ψ d ∈ center B
    rw [MonoidHom.mem_ker.mp hd]
    exact one_mem _
  have h := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  rw [← h, mul_comm]

theorem two_pow_dvd_card_center (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
    (hA : IsQuasisimple A) (hB : IsQuasisimple B) (hodd : Odd (Nat.card φ.ker)) {n : ℕ}
    (hn : 2 ^ n ∣ Nat.card (center B)) : 2 ^ n ∣ Nat.card (center A) := by
  have hM := comap_center_eq hφ hψ hA hB hodd
  have h1 := card_comap_center hφ
  have h2 := card_comap_center hψ
  rw [hM, h2] at h1
  have hd : 2 ^ n ∣ Nat.card (center A) * Nat.card φ.ker := h1 ▸ hn.mul_right _
  have hc : Nat.Coprime (2 ^ n) (Nat.card φ.ker) :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr hodd)
  exact hc.dvd_of_dvd_mul_right hd

theorem even_card_center (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
    (hA : IsQuasisimple A) (hB : IsQuasisimple B) (hodd : Odd (Nat.card φ.ker))
    (h : Even (Nat.card (center B))) : Even (Nat.card (center A)) := by
  rw [even_iff_two_dvd] at h ⊢
  simpa using two_pow_dvd_card_center (n := 1) hφ hψ hA hB hodd (by simpa using h)

@[expose] noncomputable def autBar {Q : Type*} [Group Q] (β : MulAut Q) : MulAut (Q ⧸ center Q) :=
  QuotientGroup.congr (center Q) (center Q) β (Subgroup.map_center_eq β)

theorem autBar_mk {Q : Type*} [Group Q] (β : MulAut Q) (q : Q) :
    autBar β (QuotientGroup.mk q) = QuotientGroup.mk (β q) := rfl

theorem centerQuotEquiv_conj (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
    (hA : IsQuasisimple A) (hB : IsQuasisimple B) (hodd : Odd (Nat.card φ.ker))
    {α : D → D} {β : MulAut A} {γ : MulAut B} (hαβ : ∀ d, φ (α d) = β (φ d))
    (hαγ : ∀ d, ψ (α d) = γ (ψ d)) (x : A ⧸ center A) :
    centerQuotEquiv hφ hψ hA hB hodd (autBar β x) =
      autBar γ (centerQuotEquiv hφ hψ hA hB hodd x) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨d, rfl⟩ := hφ a
  rw [autBar_mk, ← hαβ, centerQuotEquiv_mk, centerQuotEquiv_mk, autBar_mk, hαγ]

theorem exists_conj_of_conj (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
    (hA : IsQuasisimple A) (hB : IsQuasisimple B) (hodd : Odd (Nat.card φ.ker))
    {α : D → D} {β : MulAut A} {γ : MulAut B} (hαβ : ∀ d, φ (α d) = β (φ d))
    (hαγ : ∀ d, ψ (α d) = γ (ψ d)) {y : B ⧸ center B} (hy : autBar γ = MulAut.conj y) :
    autBar β = MulAut.conj ((centerQuotEquiv hφ hψ hA hB hodd).symm y) := by
  set e := centerQuotEquiv hφ hψ hA hB hodd
  ext x
  apply e.injective
  rw [centerQuotEquiv_conj hφ hψ hA hB hodd hαβ hαγ, hy, MulAut.conj_apply, MulAut.conj_apply,
    map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end FTG

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
