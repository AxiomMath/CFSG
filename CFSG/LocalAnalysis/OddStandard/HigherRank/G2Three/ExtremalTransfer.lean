module

public import CFSG.RankThree.PartTwo.Sec8.TransferExtremal

public section

namespace CFSG.OddStandard.HigherRank.G2Three

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def IsExtremalConj (P : Subgroup G) (t x : G) : Prop :=
  x ∈ P ∧ IsConj t x ∧
    ∀ y ∈ P, IsConj t y →
      Nat.card ↥(P ⊓ centralizer ({y} : Set G)) ≤ Nat.card ↥(P ⊓ centralizer ({x} : Set G))

private lemma orderOf_eq_of_isConj {a b : G} (h : IsConj a b) : orderOf b = orderOf a := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  rw [← hc]
  simpa [MulAut.conj_apply] using (MulAut.conj c).orderOf_eq a

theorem exists_isExtremalConj (P : Sylow 2 G) {t : G} (ht : orderOf t = 2) :
    ∃ x, IsExtremalConj (P : Subgroup G) t x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpt : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ht, pow_one]
  obtain ⟨Q, hQ⟩ := hpt.exists_le_sylow
  haveI : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex P
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (M := G) Q P
  have hcQ : MulAut.conj c • (Q : Subgroup G) = (P : Subgroup G) := by
    have h := congrArg (fun R : Sylow 2 G => (R : Subgroup G)) hc
    simpa [Sylow.coe_subgroup_smul] using h
  have htQ : t ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers t)
  have htP : (MulAut.conj c) t ∈ (P : Subgroup G) := by
    rw [← hcQ]
    simpa [MulAut.smul_def] using
      Subgroup.smul_mem_pointwise_smul t (MulAut.conj c) (Q : Subgroup G) htQ
  have hconj : IsConj t ((MulAut.conj c) t) := by
    rw [isConj_iff]
    exact ⟨c, by rw [MulAut.conj_apply]⟩
  let S : Set G := {y | y ∈ (P : Subgroup G) ∧ IsConj t y}
  have hSfin : S.Finite := Set.finite_univ.subset (by intro y hy; trivial)
  have hSne : S.Nonempty := ⟨(MulAut.conj c) t, htP, hconj⟩
  obtain ⟨x, hxs, hxmax⟩ :=
    Finset.exists_max_image hSfin.toFinset
      (fun y => Nat.card ↥((P : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G)))
      (hSfin.toFinset_nonempty.mpr hSne)
  have hxS : x ∈ S := hSfin.mem_toFinset.mp hxs
  exact ⟨x, hxS.1, hxS.2, fun y hyP hyconj =>
    hxmax y (hSfin.mem_toFinset.mpr ⟨hyP, hyconj⟩)⟩

theorem commutator_ne_top_of_extremalConj (P : Sylow 2 G) {N : Subgroup G}
    (hNP : N ≤ (P : Subgroup G)) [(N.subgroupOf (P : Subgroup G)).Normal]
    (hcyc : IsCyclic ((P : Subgroup G) ⧸ N.subgroupOf (P : Subgroup G))) {t : G}
    (ht : orderOf t = 2) (hext : ∀ x : G, IsExtremalConj (P : Subgroup G) t x → x ∉ N) :
    commutator G ≠ ⊤ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_isExtremalConj P ht
  have hxN : x ∉ N := hext x hx
  have hxord : orderOf x = 2 := (orderOf_eq_of_isConj hx.2.1).trans ht
  have hxp : x ^ 2 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  let U : Subgroup (P : Subgroup G) := N.subgroupOf (P : Subgroup G)
  have hUn : U.Normal := by
    change (N.subgroupOf (P : Subgroup G)).Normal
    infer_instance
  haveI : U.Normal := hUn
  let Q : Type := (P : Subgroup G) ⧸ U
  haveI : IsCyclic Q := hcyc
  letI : CommGroup Q := IsCyclic.commGroup
  have habel : ∀ y ∈ (P : Subgroup G), ∀ z ∈ (P : Subgroup G),
      y * z * y⁻¹ * z⁻¹ ∈ N := by
    intro y hy z hz
    have h1 : (QuotientGroup.mk' U)
        (⟨y, hy⟩ * ⟨z, hz⟩ * ⟨y, hy⟩⁻¹ * ⟨z, hz⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    have hmem : (⟨y, hy⟩ * ⟨z, hz⟩ * ⟨y, hy⟩⁻¹ * ⟨z, hz⟩⁻¹ : (P : Subgroup G)) ∈ U :=
      (QuotientGroup.eq_one_iff _).mp (by simpa [QuotientGroup.mk'_apply] using h1)
    simpa using Subgroup.mem_subgroupOf.mp hmem
  have hfus : ∀ g : G,
      (∀ y ∈ (P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G),
        g⁻¹ * y * g ∈ (P : Subgroup G)) →
        x⁻¹ * (g⁻¹ * x * g) ∈ N := by
    intro g hg
    have hxC : x ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hxD : x ∈ (P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) := ⟨hx.1, hxC⟩
    set x' : G := g⁻¹ * x * g with hx'
    have hx'P : x' ∈ (P : Subgroup G) := by
      rw [hx']
      exact hg x hxD
    set D' : Subgroup G :=
      (MulAut.conj g⁻¹) • ((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)) with hD'def
    have hD'P : D' ≤ (P : Subgroup G) := by
      intro z hz
      rw [hD'def] at hz
      rw [Subgroup.mem_smul_pointwise_iff_exists] at hz
      obtain ⟨d, hdD, rfl⟩ := hz
      simp only [MulAut.smul_def, MulAut.conj_apply, inv_inv]
      exact hg d hdD
    have hD'C : D' ≤ Subgroup.centralizer ({x'} : Set G) := by
      rw [hD'def]
      let f : G →* G := MulDistribMulAction.toMonoidEnd (MulAut G) G (MulAut.conj g⁻¹)
      have hmap : (Subgroup.centralizer ({x} : Set G)).map f ≤
          Subgroup.centralizer (f '' ({x} : Set G)) :=
        Subgroup.map_centralizer_le_centralizer_image _ _
      calc (MulAut.conj g⁻¹) • ((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G))
          = ((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)).map f :=
            Subgroup.pointwise_smul_def _
        _ ≤ (Subgroup.centralizer ({x} : Set G)).map f :=
            Subgroup.map_mono inf_le_right
        _ ≤ Subgroup.centralizer (f '' ({x} : Set G)) := hmap
        _ = Subgroup.centralizer ({x'} : Set G) := by
            congr 1
            ext z
            simp [f, x', MulAut.conj_apply]
    have hcardD : Nat.card ↥D' =
        Nat.card ↥((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
      (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) _).toEquiv).symm
    have hx'E : IsExtremalConj (P : Subgroup G) t x' := by
      refine ⟨hx'P, ?_, ?_⟩
      · have hxx' : IsConj x x' := by
          rw [isConj_iff]
          refine ⟨g⁻¹, ?_⟩
          rw [hx']
          simp
        exact hx.2.1.trans hxx'
      · intro y hyP hyconj
        calc Nat.card ↥((P : Subgroup G) ⊓ Subgroup.centralizer ({y} : Set G))
            ≤ Nat.card ↥((P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
              hx.2.2 y hyP hyconj
          _ = Nat.card ↥D' := hcardD.symm
          _ ≤ Nat.card ↥((P : Subgroup G) ⊓ Subgroup.centralizer ({x'} : Set G)) :=
              Subgroup.card_le_of_le (le_inf hD'P hD'C)
    have hx'N : x' ∉ N := hext x' hx'E
    have hx'ord : orderOf x' = 2 := (orderOf_eq_of_isConj hx'E.2.1).trans ht
    let a : Q := QuotientGroup.mk' U ⟨x, hx.1⟩
    let b : Q := QuotientGroup.mk' U ⟨x', hx'P⟩
    have ha2 : a ^ 2 = 1 := by
      change (QuotientGroup.mk' U ⟨x, hx.1⟩) ^ 2 = 1
      rw [← map_pow]
      have h2 : (⟨x, hx.1⟩ : (P : Subgroup G)) ^ 2 = 1 := Subtype.ext (by simpa using hxp)
      rw [h2, map_one]
    have ha_ne : a ≠ 1 := by
      intro h
      have h' : ((⟨x, hx.1⟩ : (P : Subgroup G)) : (P : Subgroup G) ⧸ U) = 1 := by
        simpa only [a, QuotientGroup.mk'_apply] using h
      exact hxN (Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (⟨x, hx.1⟩ : (P : Subgroup G))).mp h'))
    have hb2 : b ^ 2 = 1 := by
      change (QuotientGroup.mk' U ⟨x', hx'P⟩) ^ 2 = 1
      rw [← map_pow]
      have h2 : (⟨x', hx'P⟩ : (P : Subgroup G)) ^ 2 = 1 :=
        Subtype.ext (by simpa [hx'ord] using pow_orderOf_eq_one x')
      rw [h2, map_one]
    have hb_ne : b ≠ 1 := by
      intro h
      have h' : ((⟨x', hx'P⟩ : (P : Subgroup G)) : (P : Subgroup G) ⧸ U) = 1 := by
        simpa only [b, QuotientGroup.mk'_apply] using h
      exact hx'N (Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (⟨x', hx'P⟩ : (P : Subgroup G))).mp h'))
    have haord : orderOf a = 2 := orderOf_eq_prime ha2 ha_ne
    have hbord : orderOf b = 2 := orderOf_eq_prime hb2 hb_ne
    haveI : Fintype Q := Fintype.ofFinite Q
    have h2dvd : 2 ∣ Fintype.card Q := by
      rw [← haord]
      exact orderOf_dvd_card
    have hcard2 : (Finset.univ.filter (fun z : Q => orderOf z = 2)).card = 1 := by
      have h := IsCyclic.card_orderOf_eq_totient (α := Q) (d := 2) h2dvd
      simpa [Nat.totient_two] using h
    have ha_mem : a ∈ Finset.univ.filter (fun z : Q => orderOf z = 2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, haord⟩
    have hb_mem : b ∈ Finset.univ.filter (fun z : Q => orderOf z = 2) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ b, hbord⟩
    have hab : a = b := by
      obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard2
      have haz : a = z := by
        have : a ∈ ({z} : Finset Q) := by rw [← hz]; exact ha_mem
        simpa using this
      have hbz : b = z := by
        have : b ∈ ({z} : Finset Q) := by rw [← hz]; exact hb_mem
        simpa using this
      rw [haz, hbz]
    have hmemU : (⟨x, hx.1⟩ : (P : Subgroup G))⁻¹ * ⟨x', hx'P⟩ ∈ U :=
      QuotientGroup.eq.mp (by simpa [a, b, QuotientGroup.mk'_apply] using hab)
    simpa using Subgroup.mem_subgroupOf.mp hmemU
  exact CFSG.RankThree.PartTwo.Sec8.commutator_ne_top_of_extremal (p := 2)
    P habel hx.1 hxN hxp hfus

theorem transfer_extremal_cyclic [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G) {N : Subgroup G} (hNP : N ≤ (P : Subgroup G))
    [(N.subgroupOf (P : Subgroup G)).Normal]
    (hcyc : IsCyclic ((P : Subgroup G) ⧸ N.subgroupOf (P : Subgroup G))) {t : G}
    (ht : orderOf t = 2) (hext : ∀ x : G, IsExtremalConj (P : Subgroup G) t x → x ∉ N) :
    False := by
  haveI : (commutator G).Normal := by
    rw [show commutator G = ⁅(⊤ : Subgroup G), ⊤⁆ from rfl]
    infer_instance
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator G) with hbot | htop
  · obtain ⟨a, b, hab⟩ := hnonab
    exact hab (((commutator_eq_bot_iff (G := G)).mp hbot).is_comm.comm a b)
  · exact commutator_ne_top_of_extremalConj P hNP hcyc ht hext htop

end CFSG.OddStandard.HigherRank.G2Three
