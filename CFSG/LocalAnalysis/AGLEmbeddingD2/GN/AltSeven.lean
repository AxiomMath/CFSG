module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltBig
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Covered
import CFSG.HardMathSupport.Cooperstein.Coordinator.TripleA7
import CFSG.Alternating.Multipliers.Small
public import CFSG.RankThree.PerfectCover.HopfCover

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56
open scoped commutatorElement

section Transport

theorem center_data_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (f : G ≃* G')
    (hZ : Nat.card (Subgroup.center G) = 3)
    (he : Nonempty (G ⧸ Subgroup.center G ≃* alternatingGroup (Fin 7))) :
    Nat.card (Subgroup.center G') = 3 ∧
      Nonempty (G' ⧸ Subgroup.center G' ≃* alternatingGroup (Fin 7)) := by
  obtain ⟨e⟩ := he
  refine ⟨?_, ⟨(QuotientGroup.congr (Subgroup.center G) (Subgroup.center G') f
    (Subgroup.map_center_eq f)).symm.trans e⟩⟩
  rw [← hZ]
  exact (Nat.card_congr (Subgroup.centerCongr f).toEquiv).symm

end Transport

theorem card_center_dvd_six_of_alt_seven {K : Type*} [Group K]
    [Group.IsPerfect K] (e : K ⧸ Subgroup.center K ≃* alternatingGroup (Fin 7)) :
    Nat.card (Subgroup.center K) ∣ 6 := by
  let q : K →* alternatingGroup (Fin 7) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center K := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff e e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hd : Nat.card q.ker ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier (alternatingGroup (Fin 7))) := by
    rw [← CFSG.RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le]
    exact Subgroup.card_map_dvd _ _
  rwa [hker, (CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_seven).2] at hd

section Abstract

variable {V : Type} [CommGroup V] [Finite V]

theorem false_of_ffStarOffender_tripleA7 (hV : ∀ v : V, v ^ 2 = 1) {H L A : Subgroup (MulAut V)}
    (hq : CFSG.IsQuasisimple ↥L) (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (he : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 7)))
    (hLH : L ≤ H) (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) (hHA : H ≤ L ⊔ A)
    (hoff : IsFFStarOffender H A) (hAL : ¬ ∀ a ∈ A, ∀ l ∈ L, a * l = l * a) : False := by
  set P := pCoreOf 2 H with hPdef
  set W := fixV P with hWdef
  have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hPH : P ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hAH : A ≤ H := hoff.1
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hoff.2.2.1.2
  have hLperf : Group.IsPerfect ↥L := hq.1
  have hLnt : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hq
  have hLP : ∀ x ∈ L, ∀ y ∈ P, x * y = y * x := by
    have hnle : ¬ L ≤ P := fun hle =>
      Group.IsPerfect.not_isNilpotent ↥L (hP2.to_le hle).isNilpotent
    intro x hx y hy
    exact (B1Red.commute_of_normal_not_le (B1Red.isQuasisimple_to_open hq)
      (fun p hp l hl => hLn p (hPH hp) l hl)
      (fun l hl p hp => B1Red.conj_mem_pCoreOf (hLH hl) hp) hnle y hy x hx).symm
  have hLP1 : L ⊓ P = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot]
    have hxc : (⟨x, hx.1⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hLP g g.2 x hx.2)
    have h3 : x ^ 3 = 1 := by
      have := pow_card_eq_one' (G := Subgroup.center ↥L) (x := ⟨⟨x, hx.1⟩, hxc⟩)
      rw [hZ] at this
      simpa using congrArg (fun y : ↥(Subgroup.center ↥L) => ((y : ↥L) : MulAut V)) this
    obtain ⟨k, hk⟩ := hP2 ⟨x, hx.2⟩
    have h2k : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hcop : Nat.Coprime 3 (2 ^ k) := (by norm_num : Nat.Coprime 3 2).pow_right k
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h3)
      (orderOf_dvd_of_pow_eq_one h2k))
  have hAn : A ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    le_normalizer_of_conj fun a ha l hl => hLn a (hAH ha) l hl
  have hsq : ∀ x ∈ H, x ^ 2 ∈ L := fun x hx => B1Red.sq_mem_of_mem_sup hAn hA2 x (hHA hx)
  have hD : ∀ x ∈ H, Odd (orderOf x) → x ∈ L := fun x hx ho =>
    B1Red.mem_of_sq_mem_of_odd (hsq x hx) ho
  have hker : H ⊓ centSub W = P := B1Red.kernel_eq_pCoreOf hV hD hLP
  have hO2 : pCoreOf 2 (autSub H W) = ⊥ := B1Red.pCoreOf_autSub_eq_bot hker
  have hLst : L ≤ stabSub W := hLH.trans (B1Red.le_stabSub_fixV_pCoreOf H)
  let fL : ↥L →* MulAut ↥W := (resHom W).comp (Subgroup.inclusion hLst)
  have hfL_mem : ∀ l, fL l ∈ autSub L W := fun l => mem_autSub.2 ⟨⟨l, hLst l.2⟩, l.2, rfl⟩
  let φ : ↥L →* ↥(autSub L W) := fL.codRestrict _ hfL_mem
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : fL l = 1 := congrArg Subtype.val hl
    have h2 : (⟨(l : MulAut V), hLst l.2⟩ : stabSub W) ∈ (resHom W).ker := h1
    rw [ker_resHom, Subgroup.mem_subgroupOf] at h2
    have h3 : (l : MulAut V) ∈ H ⊓ centSub W := ⟨hLH l.2, h2⟩
    rw [hker] at h3
    have h4 : (l : MulAut V) ∈ L ⊓ P := ⟨l.2, h3⟩
    rw [hLP1, Subgroup.mem_bot] at h4
    exact Subtype.ext h4
  have hφsurj : Function.Surjective φ := by
    rintro ⟨ψ, hψ⟩
    obtain ⟨g, hgL, hg⟩ := mem_autSub.1 hψ
    exact ⟨⟨g.1, hgL⟩, Subtype.ext hg⟩
  let eL : ↥L ≃* ↥(autSub L W) := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  obtain ⟨hZb, heb⟩ := center_data_of_mulEquiv eL hZ he
  have hqb : CFSG.IsQuasisimple ↥(autSub L W) := CFSG.LocalCores.isQuasisimple_of_mulEquiv eL hq
  have hconj : ∀ y ∈ autSub H W, ∀ l ∈ autSub L W, y * l * y⁻¹ ∈ autSub L W :=
    fun y hy l hl => autSub_conj_mem (fun x hx y hy => hLn x hx y hy) hy hl
  have h2 : ∀ y ∈ autSub H W, ∃ k : ℕ, y ^ 2 ^ k ∈ autSub L W := by
    intro y hy
    obtain ⟨g, hgH, rfl⟩ := mem_autSub.1 hy
    refine ⟨1, mem_autSub.2 ⟨g ^ 2, hsq _ hgH, ?_⟩⟩
    simp [map_pow]
  have hFstar : quasithinGenFitting (autSub H W) = autSub L W :=
    C124.quasithinGenFitting_eq_of_two_group_quot (autSub_mono hLH W) hconj
      (Or.inl (B1Red.isQuasisimple_to_open hqb)) h2 hO2
  have hWA : commSub W A ≠ ⊥ := by
    intro h
    rw [commSub_eq_bot_iff] at h
    apply hAL
    intro a ha l hl
    have h1 : a ∈ H ⊓ centSub W := ⟨hAH ha, fun w hw => h hw a ha⟩
    rw [hker] at h1
    exact (hLP l hl a h1).symm
  have hoff' : IsFFStarOffender (autSub H W) (autSub A W) :=
    B7_1_1 hoff (fun a ha w hw => B1Red.fixV_pCoreOf_inv a (hAH ha) w hw) hWA
  exact CFSG.HardMathSupport.Cooperstein.Coordinator.gf2NoFFTripleA7 ↥W
    (fun v => Subtype.ext (hV v)) (autSub H W) (autSub L W) hFstar.symm hqb hZb heb (autSub A W)
    hoff'

end Abstract

section Reduction

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem center_eq_bot_of_alt_seven (hX : GNSetting X T)
    {L : Subgroup (X ⧸ gnC T)} (hL : IsComponentOf L ⊤)
    (hJ : ⁅L, gnImg T (thompsonJ T)⁆ = L)
    (he : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7))) :
    Subgroup.center ↥L = ⊥ := by
  obtain ⟨e⟩ := he
  have hq : CFSG.IsQuasisimple ↥L := ((CFSG.isComponent_iff_open L).2 hL).1
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.center ↥L) := not_two_dvd_card_center hX hL
  have : Group.IsPerfect ↥L := hq.1
  have hdvd : Nat.card (Subgroup.center ↥L) ∣ 6 := card_center_dvd_six_of_alt_seven e
  have hpos : 0 < Nat.card (Subgroup.center ↥L) := Nat.card_pos
  have hle : Nat.card (Subgroup.center ↥L) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have h13 : Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3 := by
    interval_cases h : Nat.card (Subgroup.center ↥L) <;> omega
  rcases h13 with h1 | h3
  · exact Subgroup.eq_bot_of_card_eq _ h1
  exfalso
  obtain ⟨A, hAmax, hLA, hAN⟩ := exists_maxElemAbelian_comm hX hL hJ
  let mk : X →* X ⧸ gnC T := QuotientGroup.mk' (gnC T)
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
  let ι : X ⧸ gnC T →* MulAut (IntMod (gnV T) hV) := gnIota hV
  have hι : Function.Injective ι := gnIota_injective hV
  have hV2 : ∀ v : IntMod (gnV T) hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  let L1 : Subgroup (MulAut (IntMod (gnV T) hV)) := L.map ι
  let A1 : Subgroup (MulAut (IntMod (gnV T) hV)) := (A.map mk).map ι
  let H : Subgroup (MulAut (IntMod (gnV T) hV)) := L1 ⊔ A1
  have hLH : L1 ≤ H := le_sup_left
  have hAH : A1 ≤ H := le_sup_right
  have hA1n : ∀ a ∈ A1, ∀ l ∈ L1, a * l * a⁻¹ ∈ L1 := by
    rintro _ ⟨q, hq, rfl⟩ _ ⟨l, hl, rfl⟩
    have := (Subgroup.mem_normalizer_iff.mp (hAN hq) l).mp hl
    exact ⟨_, this, by simp⟩
  have hA1N : A1 ≤ Subgroup.normalizer (L1 : Set _) := le_normalizer_of_conj hA1n
  have hHN : H ≤ Subgroup.normalizer (L1 : Set _) := sup_le Subgroup.le_normalizer hA1N
  have hLn : ∀ h ∈ H, ∀ l ∈ L1, h * l * h⁻¹ ∈ L1 :=
    fun h hh l hl => (Subgroup.mem_normalizer_iff.mp (hHN hh) l).mp hl
  have hLbot : L ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥L = 1 := by rw [h, Subgroup.card_bot]
    have h2 := Subgroup.card_subgroup_dvd_card (Subgroup.center ↥L)
    rw [h3, h1] at h2
    omega
  have hA1eq : A1 = autI hV A := map_mk_map_gnIota hV A
  have hTN : T ≤ Subgroup.normalizer ((gnV T : Subgroup X) : Set X) :=
    fun g _ => mem_normalizer_gnV T g
  have hA1ne : A1 ≠ ⊥ := by
    intro h
    have h1 : A.map mk = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ hι).1 h
    rw [h1, Subgroup.commutator_bot_right] at hLA
    exact hLbot hLA.symm
  have hoff : IsFFStarOffender H A1 := by
    refine ⟨hAH, hA1ne, ⟨?_, ?_⟩, ?_⟩
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      have hxy : x * y = y * x :=
        congrArg Subtype.val (hAmax.2.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      show ι (mk x) * ι (mk y) = ι (mk y) * ι (mk x)
      simp only [← map_mul, hxy]
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [← map_pow, ← map_pow]
      show ι (mk (x ^ 2)) = 1
      rw [hAmax.2.1.2 x hx, map_one, map_one]
    · intro B hB
      rw [hA1eq] at hB ⊢
      exact (offender_core hV (gnV_le T hX) hTN hAmax hB).1
  have hAL : ¬ ∀ a ∈ A1, ∀ l ∈ L1, a * l = l * a := by
    intro hc
    apply hLbot
    rw [← hLA, eq_bot_iff, Subgroup.commutator_le]
    intro l hl q hq
    rw [Subgroup.mem_bot]
    apply hι
    rw [map_commutatorElement, map_one]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (hc (ι q) ⟨q, hq, rfl⟩ (ι l) ⟨l, hl, rfl⟩).symm
  let f : ↥L ≃* ↥L1 := Subgroup.equivMapOfInjective L ι hι
  obtain ⟨hZ1, he1⟩ := center_data_of_mulEquiv f h3 ⟨e⟩
  exact false_of_ffStarOffender_tripleA7 hV2 (CFSG.LocalCores.isQuasisimple_of_mulEquiv f hq) hZ1
    he1 hLH hLn le_rfl hoff hAL

end Reduction

@[expose] def GNAltRestSeven : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T → T ≠ ⊥ →
    ∀ C₁ C₂ : Subgroup X, IsC118Pair T C₁ C₂ →
      ∀ L : Subgroup (X ⧸ gnC T), GNYComponent T C₁ C₂ L →
        Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin 7)) →
          ¬ pElementSubgroup 3 (gnA T C₁ L) ≤ (Subgroup.center ↥L).map L.subtype ∧
            (gnImg T T ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) →
              1 < Open.pRank 3 (gnA T C₁ L) ∨ 1 < Open.pRank 3 (gnA T C₂ L))

theorem gnAltRest_of_seven (h : GNAltRestSeven) : GNAltRest := by
  intro X _ _ T hX hT C₁ C₂ hP L hY he
  obtain ⟨h1, hc⟩ := h X T hX hT C₁ C₂ hP L hY he
  obtain ⟨-, h1Z, -, -, h2B, h2c, -⟩ := hP
  have hJ := commutator_eq_of_gnYComponent hX h1Z h2B h2c hY
  exact ⟨center_eq_bot_of_alt_seven hX hY.1 hJ he, h1, hc⟩

end CFSG.AGLEmbeddingD2.GN
