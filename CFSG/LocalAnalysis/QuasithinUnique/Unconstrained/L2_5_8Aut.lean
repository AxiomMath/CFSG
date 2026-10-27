module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders

public section

namespace CFSG.QuasithinUnique.Unc25Small

open CFSG.Open CFSG.Quasithin

section Abstract

variable {X : Type*} [Group X]

@[expose] def stabAut (P : Subgroup X) : Subgroup (MulAut X) where
  carrier := {φ | ∀ y, φ y ∈ P ↔ y ∈ P}
  mul_mem' := by
    intro a b ha hb y
    show a (b y) ∈ P ↔ y ∈ P
    exact (ha (b y)).trans (hb y)
  one_mem' := fun y => Iff.rfl
  inv_mem' := by
    intro a ha y
    show a⁻¹ y ∈ P ↔ y ∈ P
    have := ha (a⁻¹ y)
    have h2 : a (a⁻¹ y) = y := by simp
    rw [h2] at this
    exact this.symm

theorem mem_stabAut {P : Subgroup X} {φ : MulAut X} : φ ∈ stabAut P ↔ ∀ y, φ y ∈ P ↔ y ∈ P :=
  Iff.rfl

theorem exists_pow_two_pow_eq_one_of_mem_stabAut {P : Subgroup X} (hP : IsPGroup 2 P)
    (hNP : Subgroup.normalizer (P : Set X) ≤ P) {φ : MulAut X} (hφ : φ ∈ stabAut P)
    (hout : ∃ k : ℕ, φ ^ 2 ^ k ∈ innerAut X) : ∃ m : ℕ, φ ^ 2 ^ m = 1 := by
  obtain ⟨k, g, hg⟩ := hout
  have hmem : φ ^ 2 ^ k ∈ stabAut P := Subgroup.pow_mem _ hφ _
  have hgN : g ∈ Subgroup.normalizer (P : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have := hmem y
    rw [← hg] at this
    simpa [MulAut.conj_apply] using this.symm
  have hgP : g ∈ P := hNP hgN
  obtain ⟨j, hj⟩ := hP ⟨g, hgP⟩
  have hj' : g ^ 2 ^ j = 1 := congrArg Subtype.val hj
  refine ⟨k + j, ?_⟩
  rw [pow_add, pow_mul, ← hg, ← map_pow, hj', map_one]

end Abstract

section Sylow

variable {G : Type*} [Group G]

theorem isSylowTwoOf_inf_of_mul {H N S : Subgroup G} (hS : IsSylowTwoOf S H) (hNH : N ≤ H)
    (hprod : ∀ h ∈ H, ∃ n ∈ N, ∃ s ∈ S, h = n * s) : IsSylowTwoOf (S ⊓ N) N := by
  refine ⟨inf_le_right, hS.2.1.to_le inf_le_left, ?_⟩
  have key : ((S ⊓ N).subgroupOf N).index = (S.subgroupOf H).index := by
    unfold Subgroup.index
    let f : N ⧸ (S ⊓ N).subgroupOf N → H ⧸ S.subgroupOf H :=
      Quotient.map' (fun n : N => (⟨n, hNH n.2⟩ : H)) (by
        intro a b hab
        have h1 : a⁻¹ * b ∈ (S ⊓ N).subgroupOf N := QuotientGroup.leftRel_apply.mp hab
        rw [QuotientGroup.leftRel_apply]
        exact (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp h1).1))
    have hf : Function.Bijective f := by
      constructor
      · intro a b
        induction a using Quotient.inductionOn' with | _ a => ?_
        induction b using Quotient.inductionOn' with | _ b => ?_
        intro hab
        have h1 : (⟨(a : G), hNH a.2⟩ : H)⁻¹ * ⟨(b : G), hNH b.2⟩ ∈ S.subgroupOf H :=
          QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        refine Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp h1, ?_⟩
        exact N.mul_mem (N.inv_mem a.2) b.2
      · intro q
        induction q using Quotient.inductionOn' with | _ h => ?_
        obtain ⟨n, hn, s, hs, hh⟩ := hprod h h.2
        refine ⟨Quotient.mk'' ⟨n, hn⟩, ?_⟩
        show Quotient.mk'' (⟨n, hNH hn⟩ : H) = Quotient.mk'' h
        apply Quotient.sound'
        rw [QuotientGroup.leftRel_apply]
        refine Subgroup.mem_subgroupOf.mpr ?_
        have : ((⟨n, hNH hn⟩ : H)⁻¹ * h : H) = ⟨s, hS.1 hs⟩ := by
          apply Subtype.ext
          show n⁻¹ * (h : G) = s
          rw [hh]; group
        show ((⟨n, hNH hn⟩ : H)⁻¹ * h : H).1 ∈ S
        rw [this]; exact hs
    exact (Nat.card_congr (Equiv.ofBijective f hf))
  rw [key]; exact hS.2.2

theorem isSylowTwoOf_subgroupOf_top_iff {P K : Subgroup G} (hPK : P ≤ K) :
    IsSylowTwoOf P K ↔ IsSylowTwoOf (P.subgroupOf K) (⊤ : Subgroup ↥K) := by
  constructor
  · rintro ⟨-, h2, hidx⟩
    refine ⟨le_top, h2.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm, ?_⟩
    have h' : ¬ 2 ∣ (P.subgroupOf K).relIndex ⊤ := by
      rw [Subgroup.relIndex_top_right]; exact hidx
    exact h'
  · rintro ⟨-, h2, hidx⟩
    refine ⟨hPK, h2.of_equiv (Subgroup.subgroupOfEquivOfLe hPK), ?_⟩
    have h' : ¬ 2 ∣ (P.subgroupOf K).relIndex ⊤ := hidx
    rwa [Subgroup.relIndex_top_right] at h'

end Sylow

section AutOn

variable {G : Type} [Group G]

theorem autOn_eq_inf_normalizer (H V : Subgroup G) :
    autOn H V = autOn (H ⊓ Subgroup.normalizer (V : Set G)) V := by
  unfold autOn
  congr 1
  ext g
  simp [Subgroup.mem_subgroupOf]

theorem isSylowTwoOf_autOn_of_mul [Finite G] {H S V : Subgroup G} (hS : IsSylowTwoOf S H)
    (hprod : ∀ h ∈ H, ∃ n ∈ H ⊓ Subgroup.normalizer (V : Set G), ∃ s ∈ S, h = n * s) :
    IsSylowTwoOf (autOn S V) (autOn H V) := by
  have h1 : IsSylowTwoOf (S ⊓ (H ⊓ Subgroup.normalizer (V : Set G)))
      (H ⊓ Subgroup.normalizer (V : Set G)) :=
    isSylowTwoOf_inf_of_mul hS inf_le_left hprod
  have h2 : S ⊓ (H ⊓ Subgroup.normalizer (V : Set G)) = S ⊓ Subgroup.normalizer (V : Set G) := by
    ext x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨a, -, c⟩
      exact ⟨a, c⟩
    · rintro ⟨a, c⟩
      exact ⟨a, hS.1 a, c⟩
  rw [h2] at h1
  have h3 := Setup.isSylowTwoOf_autOn (V := V) h1 inf_le_right
  rw [autOn_eq_inf_normalizer H V, autOn_eq_inf_normalizer S V]
  exact h3

theorem autOn_le_stabAut (S K : Subgroup G) :
    autOn S K ≤ stabAut ((S ⊓ K).subgroupOf K) := by
  intro φ hφ
  obtain ⟨g, hgS, rfl⟩ := Setup.mem_autOn_iff.mp hφ
  rw [mem_stabAut]
  intro y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Setup.coe_conjAct_apply]
  have hgS' : (g : G) ∈ S := hgS
  constructor
  · intro h
    refine ⟨?_, y.2⟩
    have h1 : (g : G)⁻¹ * ((g : G) * y * (g : G)⁻¹) * (g : G) ∈ S :=
      S.mul_mem (S.mul_mem (S.inv_mem hgS') h.1) hgS'
    simpa [mul_assoc] using h1
  · intro h
    refine ⟨?_, ?_⟩
    · exact S.mul_mem (S.mul_mem hgS' h.1) (S.inv_mem hgS')
    · have := (conjAct K g y).2
      rwa [Setup.coe_conjAct_apply] at this

theorem mem_autOn_of_mem_stabAut [Finite G] {H S K : Subgroup G}
    (hsyl : IsSylowTwoOf (autOn S K) (autOn H K)) (hSH : S ≤ H)
    (hP : IsPGroup 2 ((S ⊓ K).subgroupOf K))
    (hNP : Subgroup.normalizer (((S ⊓ K).subgroupOf K : Subgroup ↥K) : Set ↥K) ≤
      (S ⊓ K).subgroupOf K)
    (hout : ∀ φ : MulAut ↥K, ∃ k : ℕ, φ ^ 2 ^ k ∈ innerAut ↥K)
    {φ : MulAut ↥K} (hφ : φ ∈ autOn H K) (hφP : φ ∈ stabAut ((S ⊓ K).subgroupOf K)) :
    φ ∈ autOn S K := by
  have : Finite (MulAut ↥K) :=
    Finite.of_injective (fun ψ : MulAut ↥K => (ψ : ↥K → ↥K))
      (fun a b h => MulEquiv.ext (congrFun h))
  have hBN : autOn S K ≤ autOn H K ⊓ stabAut ((S ⊓ K).subgroupOf K) :=
    le_inf (autOn_le_autOn K hSH) (autOn_le_stabAut S K)
  have hN2 : IsPGroup 2 ↥(autOn H K ⊓ stabAut ((S ⊓ K).subgroupOf K)) := by
    intro x
    obtain ⟨m, hm⟩ := exists_pow_two_pow_eq_one_of_mem_stabAut hP hNP x.2.2 (hout x.1)
    exact ⟨m, Subtype.ext hm⟩
  have hEq := hsyl.eq_of_le hBN inf_le_left hN2
  rw [← hEq]
  exact ⟨hφ, hφP⟩

end AutOn

section Four

variable {G : Type} [Group G]

theorem isFourSubgroup_subgroupOf {F K : Subgroup G} (hFK : F ≤ K) (hF : IsFourSubgroup F) :
    IsFourSubgroup (F.subgroupOf K) := by
  obtain ⟨⟨hc, hexp⟩, hcard⟩ := hF
  have := hc
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext; apply Subtype.ext
    exact setLike_mul_comm (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)
  · apply Subtype.ext
    have := hexp (x : G) hx
    exact this
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFK).toEquiv]
    exact hcard

theorem inf_normalizer_subgroupOf {F K : Subgroup G} (hFK : F ≤ K) :
    (K ⊓ Subgroup.normalizer (F : Set G)).subgroupOf K =
      Subgroup.normalizer (F.subgroupOf K : Set ↥K) := by
  ext k
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff,
    Subgroup.mem_normalizer_iff]
  constructor
  · rintro ⟨-, hk⟩ y
    have := hk (y : G)
    simpa [Subgroup.mem_subgroupOf] using this
  · intro hk
    refine ⟨k.2, fun g => ?_⟩
    constructor
    · intro hg
      have hgK : g ∈ K := hFK hg
      have := (hk ⟨g, hgK⟩).mp (Subgroup.mem_subgroupOf.mpr hg)
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hg
      have hgK : g ∈ K := by
        have : (k : G)⁻¹ * ((k : G) * g * (k : G)⁻¹) * (k : G) ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem k.2) (hFK hg)) k.2
        simpa [mul_assoc] using this
      have := (hk ⟨g, hgK⟩).mpr (by simpa [Subgroup.mem_subgroupOf] using hg)
      simpa [Subgroup.mem_subgroupOf] using this

noncomputable def infNormalizerEquiv {F K : Subgroup G} (hFK : F ≤ K) :
    ↥(K ⊓ Subgroup.normalizer (F : Set G)) ≃*
      ↥(Subgroup.normalizer (F.subgroupOf K : Set ↥K)) :=
  (Subgroup.subgroupOfEquivOfLe
    (inf_le_left : K ⊓ Subgroup.normalizer (F : Set G) ≤ K)).symm.trans
    (MulEquiv.subgroupCongr (inf_normalizer_subgroupOf hFK))

end Four

section Center

theorem card_center_dihedral (n : ℕ) (hn : 4 ≤ n) (hn2 : ∃ k : ℕ, n = 2 ^ k) :
    Nat.card (Subgroup.center (DihedralGroup n)) = 2 := by
  obtain ⟨k, hk⟩ := hn2
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k <;> omega
  have heven : Even n := by
    rw [hk]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk2
    exact ⟨2 ^ (2 + j - 1), by rw [← two_mul, ← pow_succ']; congr 1; omega⟩
  have hne : n ≠ 2 := by omega
  have : NeZero n := ⟨by omega⟩
  obtain ⟨m, hm⟩ := heven
  have hm' : n / 2 = m := by omega
  have hmpos : 0 < m := by omega
  have hmn : m < n := by omega
  rw [DihedralGroup.center_eq_closure_of_even_ne_two ⟨m, hm⟩ hne, Nat.card_zpowers,
    DihedralGroup.orderOf_r, hm']
  have hval : ((m : ℕ) : ZMod n).val = m := by
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hmn]
  rw [hval]
  have hg : Nat.gcd n m = m := Nat.gcd_eq_right ⟨2, by omega⟩
  rw [hg]
  exact Nat.div_eq_of_eq_mul_left hmpos (by omega)

theorem card_center_eq_two {X : Type*} [Group X] [Finite X] {P : Subgroup X} (hP : IsPGroup 2 P)
    (hshape : (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥P ≃* DihedralGroup n)) ∨
      Nonempty (↥P ≃* SemidihedralGroup 4)) :
    Nat.card (Subgroup.center ↥P) = 2 := by
  rcases hshape with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have hcard : Nat.card ↥P = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have hdvd : n ∣ 2 ^ k := ⟨2, by rw [← hk, hcard]; ring⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact card_center_dihedral n hn ⟨j, hj⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact CFSG.Semidihedral.center_card 4 (by norm_num)

end Center

end CFSG.QuasithinUnique.Unc25Small
