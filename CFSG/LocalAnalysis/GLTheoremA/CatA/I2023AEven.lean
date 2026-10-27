module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023ACtx
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023ALift
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023AFin
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2023ABs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2023

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def stabU {S : Type} [Group S] (U : Subgroup S) : Subgroup (MulAut S) where
  carrier := {φ | ∀ u, u ∈ U ↔ φ u ∈ U}
  one_mem' := fun u => Iff.rfl
  mul_mem' := by
    intro a b ha hb u
    rw [hb u, ha (b u)]
    rfl
  inv_mem' := by
    intro a ha u
    have := ha (a⁻¹ u)
    rw [show a (a⁻¹ u) = u from by simp] at this
    exact this.symm

theorem mem_stabU_of_forward {S : Type} [Group S] [Finite S] {U : Subgroup S} {φ : MulAut S}
    (h : ∀ u ∈ U, φ u ∈ U) : φ ∈ stabU U := by
  intro u
  refine ⟨h u, fun hu => ?_⟩
  let f : ↥U → ↥U := fun v => ⟨φ v, h v v.2⟩
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (φ.injective (congrArg Subtype.val hab))
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨φ u, hu⟩
  have : (v : S) = u := φ.injective (congrArg Subtype.val hv)
  rw [← this]
  exact v.2

@[expose] def preimL (L : Subgroup G) (U : Subgroup (PQuot 3 L)) : Subgroup G :=
  (U.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))).map L.subtype

theorem mem_preimL {L : Subgroup G} {U : Subgroup (PQuot 3 L)} {y : G} :
    y ∈ preimL L U ↔ ∃ l : ↥L, (QuotientGroup.mk l : PQuot 3 L) ∈ U ∧ (l : G) = y := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l, hl, rfl⟩

theorem preimL_le {L : Subgroup G} {U : Subgroup (PQuot 3 L)} : preimL L U ≤ L := by
  rintro y hy
  obtain ⟨l, -, rfl⟩ := mem_preimL.1 hy
  exact l.2

theorem card_preimL {L : Subgroup G} {U : Subgroup (PQuot 3 L)} :
    Nat.card (preimL L U) = Nat.card (GLAPPrimeCore 3 ↥L) * Nat.card U := by
  have h1 : Nat.card (preimL L U) =
      Nat.card (U.comap (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L))) :=
    Subgroup.card_map_of_injective L.subtype_injective
  rw [h1]
  exact QuotientGroup.card_preimage_mk (GLAPPrimeCore 3 ↥L) (U : Set (PQuot 3 L))

theorem not_three_dvd_card_preimL {L : Subgroup G} {U : Subgroup (PQuot 3 L)}
    (hU : IsPGroup 2 U) : ¬ 3 ∣ Nat.card (preimL L U) := by
  rw [card_preimL]
  obtain ⟨k, hk⟩ := hU.exists_card_eq
  rw [hk]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥L) h
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega

theorem starOut_even {q : TauCeti.PrimePower} {B : Subgroup G} {x : G} {L : Subgroup G}
    (hc : Ctx B x L) (F : TD4Facts (PQuot 3 L) q) (hev : Even q.exponent)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hnon : ¬ InducesInnerMod 3 L b₀) :
    ∃ (bs : G) (hbs : bs ∈ cx x),
      rho L ⟨bs, hc.hXN hbs⟩ ∉ innerAutS (PQuot 3 L) ∧
      (Nat.card {y : PQuot 3 L // rho L ⟨bs, hc.hXN hbs⟩ y = y}).factorization 2 =
        6 * q.exponent ∧
      StarOut B x L (rho L ⟨bs, hc.hXN hbs⟩) := by
  classical
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨bs, hbs, ⟨g', hg'⟩, hbs3, hψ3, hψout, hψfac, -⟩ :=
    exists_bs hc.hL hc.hXN hc.hZ F (hc.hBcx hb₀) (hc.hBel.2 b₀ hb₀) hnon
  have hbsN : bs ∈ Subgroup.normalizer (L : Set G) := hc.hXN hbs
  set ψ : MulAut (PQuot 3 L) := rho L ⟨bs, hbsN⟩ with hψ
  obtain ⟨D, hD, hD9', hDfix, U, hU2, hU8, hUψ, hUD, hψU⟩ := F.E hev ψ hψ3 hψout hψfac 2 le_rfl
  have hD9 : Nat.card D = 9 := by rw [hD9']; norm_num
  have hMD : ∀ d ∈ D, MulAut.conj d ∈ stabU U := fun d hd =>
    mem_stabU_of_forward fun u hu => by simpa using hUD d hd u hu
  have hMψ : ψ ∈ stabU U := mem_stabU_of_forward hUψ
  obtain ⟨S, hSX, hSel, hxS, ⟨n₁, hn₁, hbsS⟩, hSD, hSM⟩ :=
    exists_lift hc.hL hc.hXN hc.hx3 hbs hbs3 hD hDfix hMD hMψ
  have hSL : S ≤ Subgroup.normalizer (L : Set G) := fun s hs => hc.hXN (hSX hs)
  have hsbX : bs * n₁ ∈ cx x := hSX hbsS
  have hsbN : bs * n₁ ∈ Subgroup.normalizer (L : Set G) := hc.hXN hsbX
  have hρsb : rho L ⟨bs * n₁, hsbN⟩ = ψ := by
    refine rho_eq_of_inv_mul_mem hc.hL hbsN hsbN ?_
    simpa using hn₁
  have hψ'out : rho L ⟨bs * n₁, hsbN⟩ ∉ innerAutS (PQuot 3 L) := by
    rw [hρsb]
    exact hψout
  have hSle : Nat.card S ≤ 81 := card_le_81 hc.hCyc hc.hZ F.toTD4Rank hSL hSel
  have hDreal : ∀ d ∈ D, ∃ s ∈ S, ∃ hs : s ∈ Subgroup.normalizer (L : Set G),
      rho L ⟨s, hs⟩ = MulAut.conj d := by
    intro d hd
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective d
    obtain ⟨n, hn, hlS⟩ := hSD l hd
    refine ⟨l * n, hlS, hc.hXN (hSX hlS), ?_⟩
    rw [← rho_inner L l]
    exact rho_eq_of_inv_mul_mem hc.hL (Subgroup.le_normalizer l.2) (hc.hXN (hSX hlS))
      (by simpa using hn)
  have hSge : 81 ≤ Nat.card S :=
    card_ge_81 hc.hZ hSL hSel hxS hc.hx1 hc.hx3 hc.hxker hD9 hDreal hbsS hsbN hψ'out
  have hcardS : Nat.card S = Nat.card B := by
    rw [hc.card_B F.toTD4Rank]
    omega
  set Ut : Subgroup G := preimL L U with hUt
  have hUtL : Ut ≤ L := preimL_le
  have hSUt : ∀ s ∈ S, ∀ h ∈ Ut, s * h * s⁻¹ ∈ Ut := by
    intro s hs h hh
    obtain ⟨l, hl, rfl⟩ := mem_preimL.1 hh
    have hsN : s ∈ Subgroup.normalizer (L : Set G) := hSL hs
    have hl' : s * (l : G) * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hsN l).1 l.2
    refine mem_preimL.2 ⟨⟨s * l * s⁻¹, hl'⟩, ?_, rfl⟩
    have h1 := rho_mk' L hsN l ⟨s * l * s⁻¹, hl'⟩ rfl
    rw [← h1]
    exact ((hSM s hs hsN) (QuotientGroup.mk l)).1 hl
  obtain ⟨P, hP⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_normalizing_sylow (p := 2) (q := 3) S Ut
    (isPGroup_of_isElemAbelian hSel) hp3 hSUt (not_three_dvd_card_preimL hU2)
  set T : Subgroup G := (P : Subgroup ↥Ut).map Ut.subtype with hT
  have hTU : T ≤ Ut := Subgroup.map_subtype_le _
  have hT2 : IsPGroup 2 T := P.2.map Ut.subtype
  have hTcard : Nat.card U ≤ Nat.card T := by
    obtain ⟨a, ha⟩ := hU2.exists_card_eq
    rw [hT, Subgroup.card_map_of_injective Ut.subtype_injective, Sylow.card_eq_multiplicity P]
    have hUtc : Nat.card ↥Ut = Nat.card (GLAPPrimeCore 3 ↥L) * 2 ^ a := by
      rw [hUt, card_preimL, ha]
    rw [hUtc, ha]
    apply Nat.pow_le_pow_right (by norm_num)
    rw [Nat.factorization_mul Nat.card_pos.ne' (by positivity)]
    simp [Nat.Prime.factorization_pow Nat.prime_two]
  have hTQ : IsEmpty (T ≃* QuaternionGroup 2) := ⟨fun e => by
    have h1 := Nat.card_congr e.toEquiv
    have h2 : Nat.card (QuaternionGroup 2) = 8 := by
      rw [Nat.card_eq_fintype_card]
      exact QuaternionGroup.card
    omega⟩
  have hTU' : ∀ u ∈ U, ∃ t ∈ T, ∃ l : ↥L, (l : G) = t ∧ (QuotientGroup.mk l : PQuot 3 L) = u := by
    let f : ↥Ut →* ↥U := ((QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp
      (Subgroup.inclusion hUtL)).codRestrict U (by
        intro y
        obtain ⟨l, hl, hly⟩ := mem_preimL.1 y.2
        have : Subgroup.inclusion hUtL y = l := Subtype.ext hly.symm
        show QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (Subgroup.inclusion hUtL y) ∈ U
        rw [this]
        exact hl)
    have hf : Function.Surjective f := by
      intro u
      obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (u : PQuot 3 L)
      have hlU : (l : G) ∈ Ut := mem_preimL.2 ⟨l, hl ▸ u.2, rfl⟩
      refine ⟨⟨l, hlU⟩, Subtype.ext ?_⟩
      exact hl
    have htop : IsPGroup 2 (⊤ : Subgroup ↥U) := hU2.of_equiv Subgroup.topEquiv.symm
    have hSU : ((P.mapSurjective hf : Sylow 2 ↥U) : Subgroup ↥U) = ⊤ :=
      ((P.mapSurjective hf).3 htop le_top).symm
    rw [Sylow.coe_mapSurjective] at hSU
    intro u hu
    have hmem : (⟨u, hu⟩ : ↥U) ∈ (P : Subgroup ↥Ut).map f := by
      rw [hSU]
      trivial
    obtain ⟨p, hp, hpu⟩ := hmem
    refine ⟨(p : G), ⟨p, hp, rfl⟩, Subgroup.inclusion hUtL p, rfl, ?_⟩
    exact congrArg Subtype.val hpu
  have hTc : (⁅T, S⁆ : Subgroup G) ≠ ⊥ := by
    intro h
    have hcent : T ≤ Subgroup.centralizer (S : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    obtain ⟨u, hu, hψu⟩ := hψU
    obtain ⟨t, htT, l, hlt, hlu⟩ := hTU' u hu
    apply hψu
    have hcomm : (bs * n₁) * t = t * (bs * n₁) :=
      Subgroup.mem_centralizer_iff.1 (hcent htT) (bs * n₁) hbsS
    have hl' : (bs * n₁) * (l : G) * (bs * n₁)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 hsbN l).1 l.2
    have h1 := rho_mk' L hsbN l ⟨(bs * n₁) * l * (bs * n₁)⁻¹, hl'⟩ rfl
    rw [hρsb] at h1
    have h2 : (⟨(bs * n₁) * l * (bs * n₁)⁻¹, hl'⟩ : ↥L) = l := by
      apply Subtype.ext
      show (bs * n₁) * (l : G) * (bs * n₁)⁻¹ = (l : G)
      rw [hlt]
      exact mul_inv_eq_iff_eq_mul.2 hcomm
    rw [h2, hlu] at h1
    exact h1
  exact ⟨bs, hbs, hψout, hψfac, ⟨S, T, bs * n₁, hsbN, hSL, hSel, hxS, hcardS, hbsS, hρsb,
    hTU.trans (hUtL.trans hc.hLX), hT2, hP, hTc, hTQ⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.I2023

end
