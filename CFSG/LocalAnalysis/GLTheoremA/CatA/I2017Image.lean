module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Cent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Up7A8Spor
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma73AuxSetup
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barAut_eq_one_iff_centMod {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    barAut 3 K ⟨g, hg⟩ = 1 ↔ CentMod 3 K g := by
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.barAut_eq_one_iff hg]
  exact ⟨fun h => ⟨hg, h⟩, fun h => h.2⟩

theorem eq_one_of_pow_three_pow_two {H : Type*} [Group H] {a : H} (h3 : a ^ 3 = 1) (h2 : a ^ 2 = 1) :
    a = 1 := by
  have key : a = a ^ 3 * (a ^ 2)⁻¹ := by group
  rw [key, h3, h2]
  simp

theorem fix_all_of_fix_x {K D : Subgroup G} (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hD : IsElemAbelian 3 D) (hD9 : Nat.card ↥D = 9) {d x : G} (hd : d ∈ D) (hx : x ∈ D)
    (hdC : CentMod 3 K d) (hd1 : d ≠ 1) (hxC : ¬ CentMod 3 K x) {q : PQuot 3 K}
    (hq : barAut 3 K ⟨x, hDK hx⟩ q = q) (e : G) (he : e ∈ D) :
    barAut 3 K ⟨e, hDK he⟩ q = q := by
  classical
  let ψ : ↥D →* MulAut (PQuot 3 K) := (barAut 3 K).comp (Subgroup.inclusion hDK)
  have hψ : ∀ g : ↥D, ψ g = barAut 3 K ⟨(g : G), hDK g.2⟩ := fun g => rfl
  have hψd : ψ ⟨d, hd⟩ = 1 := (hψ ⟨d, hd⟩).trans ((barAut_eq_one_iff_centMod _).2 hdC)
  have hψx : ψ ⟨x, hx⟩ ≠ 1 := fun h => hxC ((barAut_eq_one_iff_centMod (hDK hx)).1 h)
  have hx3 : x ^ 3 = 1 := hD.2 x hx
  have hd3 : d ^ 3 = 1 := hD.2 d hd
  let M : Subgroup ↥D :=
    { carrier := {g | ψ g q = q}
      mul_mem' := fun {a b} ha hb => by
        show ψ (a * b) q = q
        rw [map_mul, MulAut.mul_apply]
        have ha' : ψ a q = q := ha
        have hb' : ψ b q = q := hb
        rw [hb', ha']
      one_mem' := by
        show ψ 1 q = q
        rw [map_one]
        rfl
      inv_mem' := fun {a} ha => by
        show ψ a⁻¹ q = q
        have ha' : ψ a q = q := ha
        rw [map_inv]
        have h2 : (ψ a) ((ψ a)⁻¹ q) = q := by
          rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
        calc (ψ a)⁻¹ q = (ψ a)⁻¹ ((ψ a) q) := by rw [ha']
          _ = q := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] }
  have hM : ∀ g : ↥D, g ∈ M ↔ ψ g q = q := fun g => Iff.rfl
  have hxM : (⟨x, hx⟩ : ↥D) ∈ M := (hM _).2 (by rw [hψ]; exact hq)
  have hx2M : (⟨x, hx⟩ : ↥D) ^ 2 ∈ M := M.pow_mem hxM 2
  have hdM : (⟨d, hd⟩ : ↥D) ∈ M := (hM _).2 (by rw [hψd]; rfl)
  have hx1 : (⟨x, hx⟩ : ↥D) ≠ 1 := by
    intro h
    apply hψx
    rw [h, map_one]
  have hx3' : (⟨x, hx⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hx2ne1 : (⟨x, hx⟩ : ↥D) ^ 2 ≠ 1 := by
    intro h
    exact hx1 (eq_one_of_pow_three_pow_two hx3' h)
  have hdx : (⟨d, hd⟩ : ↥D) ≠ (⟨x, hx⟩ : ↥D) := by
    intro h
    apply hψx
    rw [← h, hψd]
  have hdx2 : (⟨d, hd⟩ : ↥D) ≠ (⟨x, hx⟩ : ↥D) ^ 2 := by
    intro h
    apply hψx
    have hsq : ψ ⟨x, hx⟩ ^ 2 = 1 := by
      rw [← map_pow, ← h, hψd]
    have hcube : ψ ⟨x, hx⟩ ^ 3 = 1 := by
      rw [← map_pow, hx3', map_one]
    exact eq_one_of_pow_three_pow_two hcube hsq
  have hdne1 : (⟨d, hd⟩ : ↥D) ≠ 1 := fun h => hd1 (by simpa using congrArg Subtype.val h)
  have hx2x : (⟨x, hx⟩ : ↥D) ^ 2 ≠ (⟨x, hx⟩ : ↥D) := by
    intro h
    exact hx1 (mul_left_cancel (a := (⟨x, hx⟩ : ↥D)) (by rw [mul_one, ← pow_two]; exact h))
  have hsubset : (({1, ⟨x, hx⟩, (⟨x, hx⟩ : ↥D) ^ 2, ⟨d, hd⟩} : Finset ↥D) : Set ↥D) ⊆ (M : Set ↥D) := by
    intro g hg
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact M.one_mem
    · exact hxM
    · exact hx2M
    · exact hdM
  have hcard4 : ({1, ⟨x, hx⟩, (⟨x, hx⟩ : ↥D) ^ 2, ⟨d, hd⟩} : Finset ↥D).card = 4 := by
    have n1 : (1 : ↥D) ∉ ({⟨x, hx⟩, (⟨x, hx⟩ : ↥D) ^ 2, ⟨d, hd⟩} : Finset ↥D) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx1.symm, hx2ne1.symm, hdne1.symm⟩
    have n2 : (⟨x, hx⟩ : ↥D) ∉ ({(⟨x, hx⟩ : ↥D) ^ 2, ⟨d, hd⟩} : Finset ↥D) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hx2x.symm, hdx.symm⟩
    have n3 : (⟨x, hx⟩ : ↥D) ^ 2 ∉ ({⟨d, hd⟩} : Finset ↥D) := by
      simp only [Finset.mem_singleton]
      exact hdx2.symm
    rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
      Finset.card_insert_of_notMem n3, Finset.card_singleton]
  have h4 : 4 ≤ Nat.card M := by
    have h1 := Set.ncard_le_ncard hsubset (Set.toFinite _)
    rw [Set.ncard_coe_finset, hcard4] at h1
    calc 4 ≤ (M : Set ↥D).ncard := h1
      _ = Nat.card ↥M := (Nat.card_coe_set_eq _).symm
  have hdvd : Nat.card M ∣ 9 := by
    rw [← hD9]
    exact Subgroup.card_subgroup_dvd_card M
  have hc9 : Nat.card M = 9 := by
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : k ≤ 2 := by nlinarith
    interval_cases k <;> omega
  have htop : M = ⊤ := Subgroup.eq_top_of_card_eq M (by rw [hc9, hD9])
  have hmemtop : (⟨e, he⟩ : ↥D) ∈ M := by
    rw [htop]
    exact Subgroup.mem_top _
  have := (hM _).1 hmemtop
  rw [hψ] at this
  exact this

theorem i2017_component_fix {K D J : Subgroup G} (hDK : D ≤ Subgroup.normalizer (K : Set G))
    (hDp : IsPGroup 3 D) {x : G} (hx : x ∈ D)
    (hfixD : ∀ q : PQuot 3 K, barAut 3 K ⟨x, hDK hx⟩ q = q →
      ∀ (e : G) (he : e ∈ D), barAut 3 K ⟨e, hDK he⟩ q = q)
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer (D : Set G)) J) :
    GLAPComponent 3 (fixSubgroup (barAut 3 K ⟨x, hDK hx⟩)) (imageMod 3 K J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set φ : ↥K →* PQuot 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) with hφ
  set C : Subgroup ↥K := (K ⊓ Subgroup.centralizer (D : Set G)).subgroupOf K with hC
  have hJC : GLAPComponent 3 C (J.subgroupOf K) :=
    glaPComponent_subgroupOf Nat.prime_three inf_le_left hJ
  have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥K)) := CFSG.pPrimeCore_coprime_card
  have hker : Nat.Coprime 3 (Nat.card ↥(C ⊓ φ.ker)) := by
    rw [hφ, QuotientGroup.ker_mk']
    exact hcop.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
  have hmap := glaPComponent_map Nat.prime_three φ hker hJC
  have hfix : C.map φ = fixSubgroup (barAut 3 K ⟨x, hDK hx⟩) := by
    apply le_antisymm
    · rintro _ ⟨c, hc, rfl⟩
      have hcC : (c : G) ∈ Subgroup.centralizer (D : Set G) :=
        (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hc)).2
      have hcx : (x : G) * c = c * x := (Subgroup.mem_centralizer_iff.1 hcC) x hx
      have h1 : K.normalizerMonoidHom ⟨x, hDK hx⟩ c = c := by
        apply Subtype.ext
        show x * (c : G) * x⁻¹ = c
        rw [hcx]
        group
      show barAut 3 K ⟨x, hDK hx⟩ (QuotientGroup.mk c) = QuotientGroup.mk c
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, h1]
    · intro q hq
      have hq' : barAut 3 K ⟨x, hDK hx⟩ q = q := hq
      have hqK : q ∈ imageMod 3 K K := by
        obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K) q
        exact Subgroup.mem_map.2 ⟨k, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
      exact imageMod_fixed_lift hDp hDK hDK le_rfl hqK (fun e he => hfixD q hq' e he)
  have hfinal : GLAPComponent 3 (fixSubgroup (barAut 3 K ⟨x, hDK hx⟩)) ((J.subgroupOf K).map φ) := by
    rw [← hfix]
    exact hmap
  exact hfinal

theorem top_of_component_top {K : Subgroup G} {L : Subgroup (PQuot 3 K)}
    (hq : CFSG.Open.IsQuasisimple (PQuot 3 K))
    (hL : GLAPComponent 3 (⊤ : Subgroup (PQuot 3 K)) L) : L = ⊤ := by
  classical
  haveI hSimple : IsSimpleGroup (PQuot 3 K ⧸ Subgroup.center (PQuot 3 K)) := hq.2
  haveI : IsSimpleGroup ↥(⊤ : Subgroup (PQuot 3 K ⧸ Subgroup.center (PQuot 3 K))) :=
    Subgroup.topEquiv.isSimpleGroup
  set π : PQuot 3 K →* PQuot 3 K ⧸ Subgroup.center (PQuot 3 K) := QuotientGroup.mk' _ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hsn : IsSubnormal (L.map π) ((⊤ : Subgroup (PQuot 3 K)).map π) := isSubnormal_map' π hL.2.1
  rw [Subgroup.map_top_of_surjective π hπs] at hsn
  have hLne : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).1 (AltDown.nontrivial_of_glaPComponent Nat.prime_three hL)
  have hLbar : L.map π ≠ ⊥ := by
    intro h
    apply hLne
    have hcen : L ≤ Subgroup.center (PQuot 3 K) := by
      intro l hl
      have hmem : π l ∈ L.map π := Subgroup.mem_map_of_mem π hl
      rw [h, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff l).1 hmem
    have hcomm : ⁅L, L⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro l hl
      exact Subgroup.mem_centralizer_iff.2 (fun m _ => Subgroup.mem_center_iff.1 (hcen hl) m)
    rw [glaPComponent_perfect hL] at hcomm
    exact hcomm
  have hLbarTop : L.map π = ⊤ := AltDown.eq_of_isSubnormal_of_isSimpleGroup hsn hLbar
  have hsup : L ⊔ Subgroup.center (PQuot 3 K) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : π x ∈ L.map π := by
      rw [hLbarTop]
      exact Subgroup.mem_top _
    obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.1 hx
    have hz : l⁻¹ * x ∈ Subgroup.center (PQuot 3 K) := QuotientGroup.eq.1 hlx
    have hxe : x = l * (l⁻¹ * x) := (mul_inv_cancel_left l x).symm
    rw [hxe]
    exact Subgroup.mul_mem_sup hl hz
  exact up7a8_eq_top_of_sup_center hq.1 hsup

theorem isAltPType_of_mulEquiv_alt8 {Q : Type} [Group Q] [Finite Q] {L : Subgroup Q}
    (e : ↥L ≃* ↥(alternatingGroup (Fin 8))) : IsAltPType 3 L 8 := by
  classical
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup ↥L := e.isSimpleGroup
  have hcard : Nat.card ↥L = 20160 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hcore : GLAPPrimeCore 3 ↥L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 3 ↥L) with h | h
    · exact h
    · exfalso
      have hcop : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥L)) := CFSG.pPrimeCore_coprime_card
      rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv, hcard] at hcop
      have h3 : (3 : ℕ) ∣ 20160 := by norm_num
      have := Nat.Coprime.eq_one_of_dvd hcop h3
      norm_num at this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans (QuotientGroup.quotientBot.trans e)⟩

theorem eight_le_of_alt8_sub {K : Subgroup G} {L : Subgroup (PQuot 3 K)} {n : ℕ} (hn : 5 ≤ n)
    (hL : Nonempty (↥L ≃* ↥(alternatingGroup (Fin 8))))
    (eS : PSimple 3 K ≃* ↥(alternatingGroup (Fin n))) : 8 ≤ n := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨eL⟩ := hL
  have hL8 : IsAltPType 3 L 8 := isAltPType_of_mulEquiv_alt8 eL
  obtain ⟨e8⟩ := hL8
  let f : ↥L →* PSimple 3 K := (QuotientGroup.mk' (Subgroup.center (PQuot 3 K))).comp L.subtype
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz : (a : PQuot 3 K) ∈ Subgroup.center (PQuot 3 K) := (QuotientGroup.eq_one_iff _).1 ha
    have := up7a8_central_inj (by norm_num : 5 ≤ 8) e8 (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3)
      a.2 hz
    exact Subtype.ext this
  have hle := Nat.card_le_card_of_injective f hf
  have hLc : Nat.card ↥L = 20160 := by
    rw [Nat.card_congr eL.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hSc : Nat.card (PSimple 3 K) = n.factorial / 2 := by
    rw [Nat.card_congr eS.toEquiv, nat_card_alternatingGroup]
    simp
  rw [hLc, hSc] at hle
  by_contra hlt
  push Not at hlt
  have hfac : n.factorial ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
  have h7 : (7 : ℕ).factorial = 5040 := rfl
  omega

end CFSG.LocalAnalysis.GLTheoremA.I2017
