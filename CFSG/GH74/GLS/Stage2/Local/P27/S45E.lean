module

public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.Classification
public import CFSG.GH74.GLS.Stage2.Local.P27.FullStmt
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FinalTheorem
import CFSG.GH74.GLS.Stage2.Local.P34S5Frat
import CFSG.GH74.GLS.TwoThin.Equivariance
import CFSG.Assembly.GL83LieDefs
import CFSG.GH74.GLS.Stage2.Local.P34S5Clo

public section

open Subgroup CFSG CFSG.GorensteinWalter CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
open scoped commutatorElement Pointwise

namespace CFSG.GH74.GLS.Stage2.Local.P27.S45

section Generic

theorem exists_injective_hom_to_complement {G : Type*} [Group G] {N T T₁ A : Subgroup G}
    (hNT : N ≤ T) (hnorm : T ≤ normalizer (N : Set G)) (hT₁ : T₁ ≤ T) (hsup : N ⊔ T₁ = T)
    (hinf : N ⊓ T₁ = ⊥) (hA : A ≤ T) (hAN : A ⊓ N = ⊥) :
    ∃ φ : ↥A →* ↥T₁, Function.Injective φ := by
  classical
  have hNn : (N.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).2 hnorm
  set N' : Subgroup ↥T := N.subgroupOf T
  let f : ↥T₁ →* ↥T ⧸ N' := (QuotientGroup.mk' N').comp (Subgroup.inclusion hT₁)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : Subgroup.inclusion hT₁ s ∈ N' := (QuotientGroup.eq_one_iff _).1 hs
    have hsN : (s : G) ∈ N := h1
    have h2 : (s : G) ∈ N ⊓ T₁ := ⟨hsN, s.2⟩
    rw [hinf, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective q
    have hs : N' ⊔ T₁.subgroupOf T = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hNT hT₁, hsup]
      exact Subgroup.subgroupOf_self T
    have ht : t ∈ N' ⊔ T₁.subgroupOf T := by rw [hs]; exact Subgroup.mem_top t
    have ht' : t ∈ ((N' ⊔ T₁.subgroupOf T : Subgroup ↥T) : Set ↥T) := ht
    rw [Subgroup.normal_mul] at ht'
    obtain ⟨n, hn, s, hs', rfl⟩ := ht'
    refine ⟨⟨(s : G), hs'⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hT₁ ⟨(s : G), hs'⟩) = QuotientGroup.mk (n * s)
    have : Subgroup.inclusion hT₁ ⟨(s : G), hs'⟩ = s := rfl
    rw [this, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).2 hn, one_mul]
  let e : ↥T₁ ≃* ↥T ⧸ N' := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨e.symm.toMonoidHom.comp ((QuotientGroup.mk' N').comp (Subgroup.inclusion hA)), ?_⟩
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : (QuotientGroup.mk' N').comp (Subgroup.inclusion hA) a = 1 := by
    have := congrArg e ha
    simpa using this
  have h2 : Subgroup.inclusion hA a ∈ N' := (QuotientGroup.eq_one_iff _).1 h1
  have haN : (a : G) ∈ N := h2
  have h3 : (a : G) ∈ A ⊓ N := ⟨a.2, haN⟩
  rw [hAN, Subgroup.mem_bot] at h3
  exact Subtype.ext h3

end Generic

section Dihedral

theorem isDihedral_iff_two_group {Y : Type} [Group Y] (hp : IsPGroup 2 Y) :
    IsDihedral Y ↔ ∃ m : ℕ, 1 ≤ m ∧ Nonempty (Y ≃* DihedralGroup (2 ^ m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨n, k, hnk, hk2, ⟨e⟩⟩
    have hk0 : NeZero k := ⟨by omega⟩
    have : Finite Y := Finite.of_equiv _ e.symm.toEquiv
    obtain ⟨a, ha⟩ := hp.exists_card_eq
    have hcard : Nat.card Y = 2 * k := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have h2k : 2 * k = 2 ^ a := by rw [← hcard, ha]
    have ha2 : 2 ≤ a := by
      by_contra hlt
      have : a ≤ 1 := by omega
      have : 2 ^ a ≤ 2 ^ 1 := Nat.pow_le_pow_right (by omega) this
      omega
    refine ⟨a - 1, by omega, ?_⟩
    have hk : k = 2 ^ (a - 1) := by
      have : 2 ^ a = 2 * 2 ^ (a - 1) := by
        rw [← pow_succ' 2 (a - 1)]
        congr 1; omega
      omega
    subst hk
    exact ⟨e⟩
  · rintro ⟨m, hm, ⟨e⟩⟩
    refine ⟨2 * 2 ^ m, 2 ^ m, rfl, ?_, ⟨e⟩⟩
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm

theorem cyclic_or_dihedral_of_injective {Y X : Type} [Group Y] [Group X] (hX : IsDihedral X)
    (hp : IsPGroup 2 X) (φ : Y →* X) (hφ : Function.Injective φ) : IsCyclic Y ∨ IsDihedral Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm, ⟨e⟩⟩ := (isDihedral_iff_two_group hp).1 hX
  let eY : Y ≃* φ.range := MonoidHom.ofInjective hφ
  let H : Subgroup (DihedralGroup (2 ^ m)) := φ.range.map e.toMonoidHom
  let eH : φ.range ≃* H := Subgroup.equivMapOfInjective φ.range e.toMonoidHom e.injective
  have hYH : Y ≃* H := eY.trans eH
  have hYp : IsPGroup 2 Y := hp.of_injective φ hφ
  rcases subgroups_dihedral_twoGroup_cyclic_or_dihedral hm H with h | ⟨k, hk, ⟨e2⟩⟩
  · exact Or.inl ((hYH.isCyclic).2 h)
  · refine Or.inr ?_
    exact (isDihedral_iff_two_group hYp).2 ⟨k, hk, ⟨hYH.trans e2⟩⟩

theorem cyclic_or_dihedral_congr {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : IsCyclic Y ∨ IsDihedral Y) : IsCyclic Y' ∨ IsDihedral Y' := by
  rcases h with h | ⟨n, k, hnk, hk2, ⟨e'⟩⟩
  · exact Or.inl ((e.isCyclic).1 h)
  · exact Or.inr ⟨n, k, hnk, hk2, ⟨e.symm.trans e'⟩⟩

end Dihedral

section SylowTransfer

theorem hasCyclicOrDihedralSylowTwo_of_isSylowOf {G : Type} [Group G] [Finite G] {C P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P C) (h : IsCyclic ↥P ∨ IsDihedral ↥P) :
    HasCyclicOrDihedralSylowTwo ↥C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro S
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥C Q S
  have hS : (S : Subgroup ↥C) = MulAut.conj g • (Q : Subgroup ↥C) := by
    rw [← hg]; rfl
  let e1 : ↥(Q : Subgroup ↥C) ≃* ↥(MulAut.conj g • (Q : Subgroup ↥C)) :=
    Subgroup.equivSMul (MulAut.conj g) _
  have e2 : ↥(Q : Subgroup ↥C) ≃* ↥P := by
    rw [hQ]; exact Subgroup.subgroupOfEquivOfLe hP.le
  have e3 : ↥(S : Subgroup ↥C) ≃* ↥P := by
    rw [hS]; exact e1.symm.trans e2
  have h' := cyclic_or_dihedral_congr e3.symm h
  rcases h' with h' | h'
  · exact Or.inl h'
  · refine Or.inr ?_
    obtain ⟨m, hm, he⟩ := (isDihedral_iff_two_group S.isPGroup').1 h'
    exact ⟨m, hm, he⟩

end SylowTransfer

section CxKJ

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_Jx {x n : G} (hn : n ∈ centralizer ({x} : Set G)) :
    n ∈ normalizer ((Jx x : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact P34.Jx_normalized x n hn h hh
  · intro hh
    have := P34.Jx_normalized x n⁻¹ (Subgroup.inv_mem _ hn) _ hh
    simpa [mul_assoc] using this

theorem CxK_Jx_conj_mem {x n c : G} (hn : n ∈ centralizer ({x} : Set G)) (hc : c ∈ CxK x (Jx x)) :
    n * c * n⁻¹ ∈ CxK x (Jx x) := by
  obtain ⟨hcC, hcS⟩ := Subgroup.mem_inf.1 hc
  obtain ⟨hcK, hcM, hcom⟩ := hcS
  have hnJ := mem_normalizer_Jx hn
  have hnM : n ∈ normalizer ((pPrimeCoreOf 2 (Jx x) : Subgroup G) : Set G) :=
    TwoThin.mem_normalizer_pPrimeCoreOf hnJ
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hn hcC) (Subgroup.inv_mem _ hn),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hnJ hcK) (Subgroup.inv_mem _ hnJ),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hnM hcM) (Subgroup.inv_mem _ hnM), fun k hk => ?_⟩
  have h1 : ⁅k, n * c * n⁻¹⁆ = n * ⁅n⁻¹ * k * n, c⁆ * n⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [h1]
  have hk' : n⁻¹ * k * n ∈ Jx x := by
    have := P34.Jx_normalized x n⁻¹ (inv_mem hn) k hk
    simpa using this
  exact (Subgroup.mem_normalizer_iff.1 hnM _).1 (hcom _ hk')

theorem centralizer_le_normalizer_CxK_Jx (x : G) :
    centralizer ({x} : Set G) ≤ normalizer ((CxK x (Jx x) : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    exact CxK_Jx_conj_mem hn hc
  · intro hc
    have := CxK_Jx_conj_mem (inv_mem hn) hc
    simpa [mul_assoc] using this

omit [Finite G] in
theorem CxK_Jx_le (x : G) : CxK x (Jx x) ≤ centralizer ({x} : Set G) := inf_le_left

theorem x_mem_CxK_Jx (x : G) : x ∈ CxK x (Jx x) := by
  have hxC : x ∈ centralizer ({x} : Set G) := Subgroup.mem_centralizer_iff.2 (by simp)
  refine ⟨hxC, mem_normalizer_Jx hxC, TwoThin.mem_normalizer_pPrimeCoreOf (mem_normalizer_Jx hxC),
    fun k hk => ?_⟩
  have hk' : k ∈ centralizer ({x} : Set G) := P34.Jx_le_centralizer x hk
  have h := Subgroup.mem_centralizer_singleton_iff.1 hk'
  have : ⁅k, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 h
  rw [this]
  exact one_mem _

theorem inf_CxK_Jx_eq_bot {x : G} {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G)))
    (hZ : Subgroup.center (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = ⊥) :
    T ⊓ CxK x (Jx x) ⊓ Jx x = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨⟨hcT, hcC⟩, hcJ⟩ := hc
  rw [Subgroup.mem_bot]
  obtain ⟨-, -, -, hcom⟩ := hcC
  let cJ : ↥(Jx x) := ⟨c, hcJ⟩
  have hcenter : (QuotientGroup.mk cJ : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ∈
      Subgroup.center (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective g
    show QuotientGroup.mk k * QuotientGroup.mk cJ = QuotientGroup.mk cJ * QuotientGroup.mk k
    have hkc : ⁅k, cJ⁆ ∈ pPrimeCore 2 ↥(Jx x) := by
      obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.1 (hcom (k : G) k.2)
      have : o = ⁅k, cJ⁆ := Subtype.ext hoe
      rw [← this]; exact ho
    have h1 : (QuotientGroup.mk ⁅k, cJ⁆ : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hkc
    have h2 := map_commutatorElement (QuotientGroup.mk' (pPrimeCore 2 ↥(Jx x))) k cJ
    have h3 : ⁅(QuotientGroup.mk k : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)),
        (QuotientGroup.mk cJ : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x))⁆ =
        (1 : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) := by
      rw [← h1]; exact h2.symm
    exact (commutatorElement_eq_one_iff_mul_comm.1 h3)
  rw [hZ, Subgroup.mem_bot] at hcenter
  have hcO : cJ ∈ pPrimeCore 2 ↥(Jx x) := (QuotientGroup.eq_one_iff _).1 hcenter
  have hodd : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥(Jx x))) := pPrimeCore_coprime_card
  have h1 : orderOf (⟨cJ, hcO⟩ : pPrimeCore 2 ↥(Jx x)) ∣ Nat.card (pPrimeCore 2 ↥(Jx x)) :=
    orderOf_dvd_natCard _
  have h2 : orderOf c = orderOf (⟨cJ, hcO⟩ : pPrimeCore 2 ↥(Jx x)) := by
    rw [← Subgroup.orderOf_coe ⟨cJ, hcO⟩, ← Subgroup.orderOf_coe cJ]
  obtain ⟨k, hk⟩ := hT.isPGroup ⟨c, hcT⟩
  have hck : c ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have h3 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
  have h4 : orderOf c ∣ Nat.card (pPrimeCore 2 ↥(Jx x)) := h2 ▸ h1
  have h5 : Nat.Coprime (2 ^ k) (Nat.card (pPrimeCore 2 ↥(Jx x))) := Nat.Coprime.pow_left k hodd
  have h6 : orderOf c ∣ Nat.gcd (2 ^ k) (Nat.card (pPrimeCore 2 ↥(Jx x))) := Nat.dvd_gcd h3 h4
  rw [Nat.Coprime.gcd_eq_one h5] at h6
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h6)

theorem hasNormal2Compl_of_isPGroup_quotient {X : Subgroup G}
    (h : IsPGroup 2 (↥X ⧸ pPrimeCore 2 ↥X)) : HasNormal2Compl X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨pPrimeCoreOf 2 X, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have : (pPrimeCoreOf 2 X).subgroupOf X = pPrimeCore 2 ↥X := by
      unfold pPrimeCoreOf Subgroup.subgroupOf
      exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [this]
    exact pPrimeCore_normal
  · unfold pPrimeCoreOf
    rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact Nat.coprime_two_left.1 pPrimeCore_coprime_card
  · have : (pPrimeCoreOf 2 X).subgroupOf X = pPrimeCore 2 ↥X := by
      unfold pPrimeCoreOf Subgroup.subgroupOf
      exact Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [this]
    exact h.exists_card_eq

end CxKJ

section GW

theorem isPGroup_quotient_of_central_involution {Y : Type} [Group Y] [Finite Y]
    (hSyl : HasCyclicOrDihedralSylowTwo Y) {x : Y} (hx : orderOf x = 2)
    (hxc : x ∈ Subgroup.center Y) : IsPGroup 2 (Y ⧸ pPrimeCore 2 Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hcyc : ∀ S : Sylow 2 Y, IsCyclic S
  ·
    have hcomp : HasNormalPComplement 2 Y := by
      by_cases h2 : 2 ∣ Nat.card Y
      · let S : Sylow 2 Y := Classical.choice Sylow.nonempty
        have hmin : (Nat.card Y).minFac = 2 := (Nat.minFac_eq_two_iff (Nat.card Y)).2 h2
        have hNC : Subgroup.normalizer (S : Set Y) ≤ Subgroup.centralizer (S : Set Y) :=
          (hcyc S).normalizer_le_centralizer hmin
        have hScenter : (S : Subgroup Y) ≤ centerIn (G := Y) (Subgroup.normalizer (S : Subgroup Y)) := by
          intro s hs
          refine ⟨Subgroup.le_normalizer hs, ?_⟩
          change s ∈ Subgroup.centralizer (Subgroup.normalizer (S : Set Y) : Set Y)
          rw [Subgroup.mem_centralizer_iff]
          intro g hg
          exact (Subgroup.mem_centralizer_iff.mp (hNC hg) s hs).symm
        exact hasNormalPComplement_of_sylow_le_center_normalizer (G := Y) 2 S hScenter
      · have hodd : Odd (Nat.card Y) := by
          rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
          exact h2
        refine ⟨⊤, inferInstance, ?_, ?_⟩
        · simpa using hodd.coprime_two_left
        · intro y
          refine ⟨0, ?_⟩
          have hsub : Subsingleton (Y ⧸ (⊤ : Subgroup Y)) := QuotientGroup.subsingleton_quotient_top
          simpa using (@Subsingleton.elim _ hsub y 1)
    exact isPGroup_quotient_pPrimeCore_of_hasNormalPComplement (p := 2) Y hcomp
  · have hdih := hasDihedralSylowTwo_of_hasCyclicOrDihedralSylowTwo_of_not_cyclic hSyl hcyc
    have hD : IsDGroup Y := gorensteinWalter Y hdih
    have hxO : x ∉ pPrimeCore 2 Y := by
      intro h
      have hodd : Odd (Nat.card (pPrimeCore 2 Y)) :=
        Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := Y))
      have h1 : orderOf (⟨x, h⟩ : pPrimeCore 2 Y) ∣ Nat.card (pPrimeCore 2 Y) := orderOf_dvd_natCard _
      have h2 : orderOf (⟨x, h⟩ : pPrimeCore 2 Y) = 2 := by
        rw [← Subgroup.orderOf_coe]; exact hx
      rw [h2] at h1
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h1)
    set xb : Y ⧸ pPrimeCore 2 Y := QuotientGroup.mk x with hxb
    have hxb1 : xb ≠ 1 := fun h => hxO ((QuotientGroup.eq_one_iff x).1 h)
    have hxbc : xb ∈ Subgroup.center (Y ⧸ pPrimeCore 2 Y) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
      show QuotientGroup.mk y * QuotientGroup.mk x = QuotientGroup.mk x * QuotientGroup.mk y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (Subgroup.mem_center_iff.1 hxc y)]
    have hxb2 : xb * xb = 1 := by
      rw [hxb, ← QuotientGroup.mk_mul]
      have := pow_orderOf_eq_one x
      rw [hx, pow_two] at this
      rw [this]; rfl
    rcases hD with ⟨-, hTwo⟩ | ⟨-, ⟨e7⟩⟩ | ⟨-, K, hK, L, hLn, hLodd, hLmodel⟩
    · exact hTwo
    · exfalso
      have hZ : Subgroup.center (Y ⧸ pPrimeCore 2 Y) = ⊥ :=
        center_eq_bot_of_mulEquiv e7 (alternatingGroup.center_eq_bot (by simp))
      exact hxb1 (Subgroup.mem_bot.1 (hZ ▸ hxbc))
    · exfalso
      have hxL : xb ∈ L := by
        have hq : Odd (Nat.card ((Y ⧸ pPrimeCore 2 Y) ⧸ L)) := by
          rw [← Subgroup.index_eq_card]; exact hLodd
        have h1 : orderOf (QuotientGroup.mk xb : (Y ⧸ pPrimeCore 2 Y) ⧸ L) ∣ 2 := by
          apply orderOf_dvd_of_pow_eq_one
          rw [pow_two, ← QuotientGroup.mk_mul, hxb2]; rfl
        have h2 : orderOf (QuotientGroup.mk xb : (Y ⧸ pPrimeCore 2 Y) ⧸ L) ∣
            Nat.card ((Y ⧸ pPrimeCore 2 Y) ⧸ L) := orderOf_dvd_natCard _
        have h3 : orderOf (QuotientGroup.mk xb : (Y ⧸ pPrimeCore 2 Y) ⧸ L) = 1 := by
          have hcop : Nat.Coprime 2 (Nat.card ((Y ⧸ pPrimeCore 2 Y) ⧸ L)) := Nat.coprime_two_left.2 hq
          have h5 := Nat.dvd_gcd h1 h2
          rw [Nat.Coprime.gcd_eq_one hcop] at h5
          exact Nat.dvd_one.1 h5
        rw [orderOf_eq_one_iff] at h3
        exact (QuotientGroup.eq_one_iff xb).1 h3
      have hZL : Subgroup.center ↥L = ⊥ := by
        rcases hLmodel with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
        · exact center_eq_bot_of_mulEquiv e (psl2_center_eq_bot K)
        · exact center_eq_bot_of_mulEquiv e (pgl2_center_eq_bot K)
      have : (⟨xb, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        exact Subgroup.mem_center_iff.1 hxbc (g : Y ⧸ pPrimeCore 2 Y)
      rw [hZL, Subgroup.mem_bot] at this
      exact hxb1 (congrArg Subtype.val this)

end GW

section Main

variable {G : Type} [Group G] [Finite G]

theorem fullE_of_T1 {x : G} {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({x} : Set G))) (hx2 : orderOf x = 2)
    (hZ : Subgroup.center (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = ⊥)
    (hT1 : ∃ T₁ : Subgroup G, T₁ ≤ T ∧ (T ⊓ Jx x) ⊔ T₁ = T ∧ T₁ ⊓ Jx x = ⊥ ∧ IsDihedral ↥T₁) :
    FullE x T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : CFSG.ABGLocalTools.IsSylowOf 2 (T ⊓ CxK x (Jx x)) (CxK x (Jx x)) :=
    hT.inf_of_le_normalizer (CxK_Jx_le x) (centralizer_le_normalizer_CxK_Jx x)
  have hcd : IsCyclic ↥(T ⊓ CxK x (Jx x)) ∨ IsDihedral ↥(T ⊓ CxK x (Jx x)) := by
    obtain ⟨T₁, hT₁T, hsup, hinf, hdih⟩ := hT1
    have hTC : T ≤ centralizer ({x} : Set G) := hT.le
    have hnorm : T ≤ normalizer ((T ⊓ Jx x : Subgroup G) : Set G) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have htJ := mem_normalizer_Jx (hTC ht)
      constructor
      · rintro ⟨hhT, hhJ⟩
        exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hhT) (Subgroup.inv_mem _ ht),
          (Subgroup.mem_normalizer_iff.1 htJ h).1 hhJ⟩
      · rintro ⟨hhT, hhJ⟩
        refine ⟨?_, (Subgroup.mem_normalizer_iff.1 htJ h).2 hhJ⟩
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ht) hhT) ht
        simpa [mul_assoc] using this
    have hN1 : (T ⊓ Jx x) ⊓ T₁ = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have h1 : g ∈ T₁ ⊓ Jx x := ⟨hg.2, hg.1.2⟩
      rw [hinf] at h1
      exact h1
    have hsup' : (T ⊓ Jx x) ⊔ T₁ = T := hsup
    have hAN : (T ⊓ CxK x (Jx x)) ⊓ (T ⊓ Jx x) = ⊥ := by
      rw [eq_bot_iff, ← inf_CxK_Jx_eq_bot hT hZ]
      intro g hg
      exact ⟨⟨hg.1.1, hg.1.2⟩, hg.2.2⟩
    obtain ⟨φ, hφ⟩ := exists_injective_hom_to_complement (N := T ⊓ Jx x) (T := T) (T₁ := T₁)
      (A := T ⊓ CxK x (Jx x)) inf_le_left hnorm hT₁T hsup' hN1 inf_le_left hAN
    have hp : IsPGroup 2 ↥T₁ := hT.isPGroup.to_le hT₁T
    exact cyclic_or_dihedral_of_injective hdih hp φ hφ
  refine ⟨?_, hcd⟩
  have hcdS : HasCyclicOrDihedralSylowTwo ↥(CxK x (Jx x)) :=
    hasCyclicOrDihedralSylowTwo_of_isSylowOf hP hcd
  have hx' : orderOf (⟨x, x_mem_CxK_Jx x⟩ : ↥(CxK x (Jx x))) = 2 := by
    rw [← hx2]; exact (Subgroup.orderOf_coe _).symm
  have hxc : (⟨x, x_mem_CxK_Jx x⟩ : ↥(CxK x (Jx x))) ∈ Subgroup.center ↥(CxK x (Jx x)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.1 (CxK_Jx_le x g.2)
  exact hasNormal2Compl_of_isPGroup_quotient
    (isPGroup_quotient_of_central_involution hcdS hx' hxc)

end Main

section Center

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_isL2 {X : Type} [Group X] {P : ℕ → Prop} (h : IVK.IsL2 X P) :
    Subgroup.center X = ⊥ := by
  obtain ⟨F, _, _, -, ⟨e⟩⟩ := h
  exact center_eq_bot_of_mulEquiv e
    (center_eq_bot_of_mulEquiv (IVK.L2.equivPSL F) (psl2_center_eq_bot F))

omit [Finite G] in
theorem center_bot_of_fullCL4 {x : G} {q : ℕ} (h : FullCL4 x q) :
    Subgroup.center (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = ⊥ := by
  rcases h with h | ⟨-, ⟨e⟩⟩
  · exact center_eq_bot_of_isL2 h
  · exact center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by simp))

end Center

end CFSG.GH74.GLS.Stage2.Local.P27.S45
