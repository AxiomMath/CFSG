module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.GroupTheory.WielandtProductAux
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPCov

open CFSG.Open Subgroup

variable {A : Type*} [Group A] [Finite A]

theorem prime_dvd_card_of_isPGroup {f : ℕ} [Fact f.Prime] {X : Subgroup A} (hX : IsPGroup f X)
    (hne : X ≠ ⊥) : f ∣ Nat.card X := by
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
  rw [hn]
  exact dvd_pow_self f hn0

theorem exists_mem_normalizer_not_mem_of_lt {r : ℕ} [Fact r.Prime] {X T : Subgroup A}
    (hT : IsPGroup r T) (hXT : X < T) :
    ∃ x ∈ T, x ∈ normalizer (X : Set A) ∧ x ∉ X := by
  have hne : X.subgroupOf T ≠ ⊤ := fun htop =>
    absurd (fun x hxT => (Subgroup.mem_subgroupOf.mp (htop ▸ trivial : (⟨x, hxT⟩ : T) ∈
      X.subgroupOf T))) (not_le_of_gt hXT)
  have : Group.IsNilpotent T := hT.isNilpotent
  have hnc : NormalizerCondition T := Group.normalizerCondition_of_isNilpotent (G := T)
  have hlt : X.subgroupOf T < Subgroup.normalizer ((X.subgroupOf T : Subgroup T) : Set T) :=
    hnc _ (lt_top_iff_ne_top.mpr hne)
  obtain ⟨x, hxN, hxnot⟩ := IsConcreteLE.exists_of_lt hlt
  refine ⟨x, x.2, ?_, fun hxA => hxnot (Subgroup.mem_subgroupOf.mpr hxA)⟩
  have hxsub : x ∈ (Subgroup.normalizer (X : Set A)).subgroupOf T := by
    rw [Subgroup.subgroupOf_normalizer_eq hXT.le]
    exact hxN
  exact Subgroup.mem_subgroupOf.mp hxsub

theorem normalizer_inf_le {K K₀ X : Subgroup A} {f : ℕ} [Fact f.Prime]
    (hSE : ∀ g ∈ K, g ∉ K₀ →
      ¬ f ∣ Nat.card ↥(K₀ ⊓ K₀.map (MulAut.conj g⁻¹).toMonoidHom))
    (hXK₀ : X ≤ K₀) (hX : IsPGroup f X) (hne : X ≠ ⊥) :
    normalizer (X : Set A) ⊓ K ≤ K₀ := by
  rintro g ⟨hgN, hgK⟩
  by_contra hgK₀
  refine hSE g hgK hgK₀
    ((prime_dvd_card_of_isPGroup hX hne).trans (Subgroup.card_dvd_of_le ?_))
  refine le_inf hXK₀ fun x hx => ?_
  refine ⟨g * x * g⁻¹, hXK₀ ((Subgroup.mem_normalizer_iff.mp hgN x).mp hx), ?_⟩
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
  group

theorem le_of_inf_ne_bot {K K₀ F : Subgroup A} {f : ℕ} [Fact f.Prime]
    (hSE : ∀ g ∈ K, g ∉ K₀ →
      ¬ f ∣ Nat.card ↥(K₀ ⊓ K₀.map (MulAut.conj g⁻¹).toMonoidHom))
    (hFK : F ≤ K) (hF : IsPGroup f F) (hne : F ⊓ K₀ ≠ ⊥) : F ≤ K₀ := by
  by_contra hFK₀
  have hlt : F ⊓ K₀ < F := lt_of_le_of_ne inf_le_left fun h => hFK₀ (h ▸ inf_le_right)
  obtain ⟨x, hxF, hxN, hxD⟩ := exists_mem_normalizer_not_mem_of_lt hF hlt
  have hxK₀ : x ∈ K₀ :=
    normalizer_inf_le hSE inf_le_right (hF.to_le inf_le_left) hne ⟨hxN, hFK hxF⟩
  exact hxD ⟨hxF, hxK₀⟩

theorem exists_conj_inf_dvd {K K₀ : Subgroup A} {f : ℕ} [hf : Fact f.Prime] (hK₀K : K₀ ≤ K)
    (hne : K₀ ≠ K) (hfK₀ : f ∣ Nat.card K₀) (hrank : 2 ≤ CFSG.Open.pRank f K)
    (hgen : ∀ E : Subgroup A, E ≤ K₀ → IsElemAbelian f E → Nat.card E = f ^ 2 →
      K ≤ Subgroup.closure {k : A | k ∈ K ∧ ∃ F : Subgroup A, F ≤ E ∧ F.relIndex E = f ∧
        ∀ y ∈ F, y * k = k * y}) :
    ∃ g ∈ K, g ∉ K₀ ∧ f ∣ Nat.card ↥(K₀ ⊓ K₀.map (MulAut.conj g⁻¹).toMonoidHom) := by
  by_contra hcon
  have hSE : ∀ g ∈ K, g ∉ K₀ →
      ¬ f ∣ Nat.card ↥(K₀ ⊓ K₀.map (MulAut.conj g⁻¹).toMonoidHom) :=
    fun g hg hg' hd => hcon ⟨g, hg, hg', hd⟩
  have hp1 : 1 < f := hf.out.one_lt
  have hf0 : 0 < f := hf.out.pos
  obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K₀) f hfK₀
  set u₁ : ↥K := ⟨(u₀ : A), hK₀K u₀.2⟩ with hu₁
  have hu₁ord : orderOf u₁ = f :=
    calc orderOf u₁ = orderOf (u₁ : A) := (Subgroup.orderOf_coe u₁).symm
      _ = orderOf (u₀ : A) := rfl
      _ = orderOf u₀ := Subgroup.orderOf_coe u₀
      _ = f := hu₀
  have hZ : IsPGroup f (Subgroup.zpowers u₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu₁ord, pow_one])
  obtain ⟨Q, hQ⟩ := hZ.exists_le_sylow
  set F₂ : Subgroup A := (Q : Subgroup ↥K).map K.subtype with hF₂
  have hF₂K : F₂ ≤ K := Subgroup.map_subtype_le _
  have hF₂p : IsPGroup f F₂ := Q.isPGroup'.map K.subtype
  have huF₂ : (u₀ : A) ∈ F₂ := ⟨u₁, hQ (Subgroup.mem_zpowers u₁), rfl⟩
  have hF₂ne : F₂ ⊓ K₀ ≠ ⊥ := by
    intro h
    have hmem : (u₀ : A) ∈ F₂ ⊓ K₀ := ⟨huF₂, u₀.2⟩
    rw [h, Subgroup.mem_bot] at hmem
    have h1 : orderOf (u₀ : A) = 1 := by rw [hmem, orderOf_one]
    rw [Subgroup.orderOf_coe, hu₀] at h1
    exact hp1.ne' h1
  have hF₂K₀ : F₂ ≤ K₀ := le_of_inf_ne_bot hSE hF₂K hF₂p hF₂ne
  have hQrank : 2 ≤ CFSG.Open.pRank f (Q : Subgroup ↥K) := by
    have h1 := (CFSG.SectionRank.pRank_sylow Q).1
    have h2 := CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := f) K
    omega
  obtain ⟨E₁, hE₁Q, hE₁ab, hE₁card⟩ := CFSG.SectionRank.exists_pRank hp1 (Q : Subgroup ↥K)
  set E₃ : Subgroup A := E₁.map K.subtype with hE₃
  have hE₃ab : IsElemAbelian f E₃ := hE₁ab.map K.subtype
  have hE₃card : Nat.card E₃ = f ^ CFSG.Open.pRank f (Q : Subgroup ↥K) := by
    rw [hE₃, Subgroup.card_map_of_injective K.subtype_injective, hE₁card]
  have hE₃K₀ : E₃ ≤ K₀ := (Subgroup.map_mono hE₁Q).trans hF₂K₀
  obtain ⟨E₄, hE₄⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E₃) f (n := 2)
    (by rw [hE₃card]; exact pow_dvd_pow f hQrank)
  set E : Subgroup A := E₄.map E₃.subtype with hE
  have hEE₃ : E ≤ E₃ := Subgroup.map_subtype_le _
  have hEK₀ : E ≤ K₀ := hEE₃.trans hE₃K₀
  have hEab : IsElemAbelian f E := hE₃ab.mono hEE₃
  have hEcard : Nat.card E = f ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective E₃.subtype_injective, hE₄]
  have hS : Subgroup.closure {k : A | k ∈ K ∧ ∃ F : Subgroup A, F ≤ E ∧ F.relIndex E = f ∧
      ∀ y ∈ F, y * k = k * y} ≤ K₀ := by
    rw [Subgroup.closure_le]
    rintro k ⟨hkK, F, hFE, hrel, hcomm⟩
    have hFcard : Nat.card F = f := by
      have h := Subgroup.relIndex_mul_card (H := F) (K := E)
      rw [inf_eq_left.mpr hFE, hrel, hEcard] at h
      exact Nat.eq_of_mul_eq_mul_left hf0 (by rw [h]; ring)
    have hFne : F ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hFcard
      exact hp1.ne hFcard
    have hkN : k ∈ normalizer (F : Set A) :=
      Subgroup.centralizer_le_normalizer (F : Set A) (Subgroup.mem_centralizer_iff.mpr hcomm)
    exact normalizer_inf_le hSE (hFE.trans hEK₀) (hEab.mono hFE).isPGroup hFne ⟨hkN, hkK⟩
  exact hne (le_antisymm hK₀K ((hgen E hEK₀ hEab hEcard).trans hS))

theorem mem_zpowers_of_isPGroup_pRank_le_one {K B : Subgroup A} {p : ℕ} [Fact p.Prime]
    (hK : CFSG.Open.pRank p K ≤ 1) (hB : IsPGroup p B) (hBK : B ≤ K) {x y : A} (hxB : x ∈ B)
    (hyB : y ∈ B) (hx : orderOf x = p) (hy : orderOf y = p) : y ∈ Subgroup.zpowers x := by
  have hp : p.Prime := Fact.out
  have hBne : B ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.mem_bot.mp hxB, orderOf_one] at hx
    exact hp.one_lt.ne hx
  obtain ⟨c, hcB, hcord, hccent⟩ :=
    CFSG.GroupTheory.WielandtProduct.exists_orderOf_eq_commute_of_isPGroup hB hBne
  have hccard : Nat.card (Subgroup.zpowers c) = p := by rw [Nat.card_zpowers, hcord]
  have key : ∀ w ∈ B, orderOf w = p → w ∈ Subgroup.zpowers c := by
    intro w hwB hw
    by_contra hwc
    obtain ⟨hea, hcard⟩ := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute hccard hw hwc
      fun a ha => by
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        exact ((hccent w hwB).zpow_left n).eq
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers w ≤ K :=
      sup_le (Subgroup.zpowers_le.mpr (hBK hcB)) (Subgroup.zpowers_le.mpr (hBK hwB))
    have h2 := CFSG.SectionRank.le_pRank hp.one_lt hle hea hcard
    omega
  have hxc := key x hxB hx
  have hyc := key y hyB hy
  have heq : Subgroup.zpowers x = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxc)
      (by rw [hccard, Nat.card_zpowers, hx])
  rw [heq]
  exact hyc

theorem mem_of_normal_of_dvd {K₀ H : Subgroup A} {p : ℕ} [hp : Fact p.Prime]
    (hK₀ : CFSG.Open.pRank p K₀ ≤ 1) (hHK₀ : H ≤ K₀) (hHn : (H.subgroupOf K₀).Normal)
    (hpH : p ∣ Nat.card H) {z : A} (hzK₀ : z ∈ K₀) (hz : orderOf z = p) : z ∈ H := by
  set z₁ : ↥K₀ := ⟨z, hzK₀⟩ with hz₁
  have hz₁ord : orderOf z₁ = p := by
    rw [← hz, ← Subgroup.orderOf_coe z₁]
  have hZ : IsPGroup p (Subgroup.zpowers z₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz₁ord, pow_one])
  obtain ⟨Q, hQ⟩ := hZ.exists_le_sylow
  set P : Subgroup A := (Q : Subgroup ↥K₀).map K₀.subtype with hP
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p P K₀ := ⟨Q, rfl⟩
  have hzP : z ∈ P := ⟨z₁, hQ (Subgroup.mem_zpowers z₁), rfl⟩
  have hHN : K₀ ≤ normalizer (H : Set A) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHK₀).mp hHn
  have hPH := hPsyl.inf_of_le_normalizer hHK₀ hHN
  have hfac : 1 ≤ (Nat.card H).factorization p :=
    (hp.out.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hpH
  have hdvd : p ∣ Nat.card ↥(P ⊓ H) := by
    rw [hPH.card_eq]
    exact dvd_pow_self p (by omega)
  obtain ⟨h₀, hh₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P ⊓ H)) p hdvd
  have hhord : orderOf (h₀ : A) = p := by rw [Subgroup.orderOf_coe, hh₀]
  have hzh : z ∈ Subgroup.zpowers (h₀ : A) :=
    mem_zpowers_of_isPGroup_pRank_le_one hK₀ hPsyl.isPGroup hPsyl.le h₀.2.1 hzP hhord hz
  exact Subgroup.zpowers_le.mpr h₀.2.2 hzh

end KPCov

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
