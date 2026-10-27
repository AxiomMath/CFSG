module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Core
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Facts
public import CFSG.LocalAnalysis.GLTheoremA.S6.Prop65Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isPGroup_zpowers_of_pow {p : ℕ} {x : G} (hx : x ^ p = 1) : IsPGroup p (Subgroup.zpowers x) := by
  intro g
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 g.2
  refine ⟨1, Subtype.ext ?_⟩
  have hpow : (x ^ n) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  rw [pow_one, Subgroup.coe_pow, ← hn, hpow]
  rfl

theorem layer_ne_bot_of_component {p : ℕ} {X M : Subgroup G} (hM : GLAPComponent p X M) :
    GLAPLayer p X ≠ ⊥ := by
  intro h
  apply component_ne_bot hM
  have hle : M ≤ GLAPLayer p X := le_sSup hM
  rw [h] at hle
  exact le_bot_iff.1 hle

theorem exists_component_of_layer_ne_bot {p : ℕ} {X : Subgroup G} (h : GLAPLayer p X ≠ ⊥) :
    ∃ M : Subgroup G, GLAPComponent p X M := by
  by_contra hno
  apply h
  have hE : {L : Subgroup G | GLAPComponent p X L} = ∅ := by
    ext T
    exact ⟨fun hT => hno ⟨T, hT⟩, fun hT => hT.elim⟩
  unfold GLAPLayer
  rw [hE, sSup_empty]

theorem normalizer_of_commute {A : Subgroup G} {g : G} (h : ∀ a ∈ A, g * a = a * g) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have e : g * k * g⁻¹ = k := by
      rw [h k hk]
      group
    rw [e]
    exact hk
  · intro hk
    have hc := h (g * k * g⁻¹) hk
    have e2 : g⁻¹ * (g * k * g⁻¹) * g = g * k * g⁻¹ := by
      rw [show g⁻¹ * (g * k * g⁻¹) * g = g⁻¹ * ((g * k * g⁻¹) * g) by group, ← hc]
      group
    have hka : k = g * k * g⁻¹ := by
      rw [← e2]
      group
    rw [hka]
    exact hk

theorem core_of_choice {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hBel : IsElemAbelian p B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hcomp : GLAPComponent p (Subgroup.centralizer ({x} : Set G)) L)
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hcm : CentModEqZpowers p B L x)
    (hZ : Subgroup.center (PQuot p L) = ⊥)
    (JType : Subgroup (PQuot p L) → Prop)
    (hch : H81Choice p (((B ⊓ L).subgroupOf L).map (QuotientGroup.mk' (GLAPPrimeCore p ↥L))) JType) :
    ∃ y ∈ B ⊓ L, y ≠ 1 ∧ ∃ J E : Subgroup G,
      GLAPLayer p (L ⊓ Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) = J ∧
      GLAPComponent p (L ⊓ Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) J ∧
      (∀ b ∈ B, CentMod p J b ↔ b ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) ∧
      E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ≤ E ∧
      GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ ∧
      ∃ JH : Subgroup (PQuot p L), JType JH ∧ Nonempty (PQuot p J ≃* PQuot p JH) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hxL : ∀ l ∈ L, x * l = l * x := fun l hl =>
    Subgroup.mem_centralizer_iff.1 (hcomp.1 hl) x (Set.mem_singleton _)
  have hxL1 : Subgroup.zpowers x ⊓ L = ⊥ :=
    P65.zpowers_inf_eq_bot_of_center hp hcomp hxB hBel hx1 hZ
  have hxp : x ^ p = 1 := hBel.2 x hxB
  obtain ⟨yy, hyyP, hyy1, JH, hJH, hJHu, hJT, ⟨zz, hzzP, hzzD, hzzL⟩, hαfact⟩ := hch
  obtain ⟨yK, hyK, rfl⟩ := Subgroup.mem_map.1 hyyP
  obtain ⟨zK, hzK, rfl⟩ := Subgroup.mem_map.1 hzzP
  have hyBL : ((yK : ↥L) : G) ∈ B ⊓ L := Subgroup.mem_subgroupOf.1 hyK
  have hzBL : ((zK : ↥L) : G) ∈ B ⊓ L := Subgroup.mem_subgroupOf.1 hzK
  set y : G := ((yK : ↥L) : G) with hy_def
  set z : G := ((zK : ↥L) : G) with hz_def
  have hyB : y ∈ B := (Subgroup.mem_inf.1 hyBL).1
  have hzB : z ∈ B := (Subgroup.mem_inf.1 hzBL).1
  have hyL : y ∈ L := (Subgroup.mem_inf.1 hyBL).2
  have hzL : z ∈ L := (Subgroup.mem_inf.1 hzBL).2
  have hyp : y ^ p = 1 := hBel.2 y hyB
  have hzp : z ^ p = 1 := hBel.2 z hzB
  have hy1 : y ≠ 1 := by
    intro h
    apply hyy1
    rw [show yK = 1 from Subtype.ext h, map_one]
  have hz1 : z ≠ 1 := by
    intro h
    apply hzzD
    rw [show zK = 1 from Subtype.ext h, map_one]
    exact Subgroup.one_mem _
  have hyK_pow : yK ^ p = 1 := Subtype.ext (by simpa using hyp)
  have hzK_pow : zK ^ p = 1 := Subtype.ext (by simpa using hzp)
  have hyx : y ∉ Subgroup.zpowers x := fun h => hy1 (by
    have hm : y ∈ Subgroup.zpowers x ⊓ L := Subgroup.mem_inf.2 ⟨h, hyL⟩
    rw [hxL1] at hm
    exact Subgroup.mem_bot.1 hm)
  have hDcard : Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = p ^ 2 :=
    P65.card_sup_zpowers hp hxp hyp hx1 hy1 hyx (isElemAbelian_commute hBel hxB hyB)
  have hDB : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ≤ B :=
    sup_le (Subgroup.zpowers_le.2 hxB) (Subgroup.zpowers_le.2 hyB)
  have hxy_norm : Subgroup.zpowers x ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 (normalizer_of_commute fun a ha =>
      isElemAbelian_commute hBel hxB ((Subgroup.zpowers_le.2 hyB) ha))
  have hset : ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) =
      (Subgroup.zpowers x : Set G) * (Subgroup.zpowers y : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ hxy_norm
  have hD_eq : L ⊓ Subgroup.centralizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext g
    constructor
    · rintro ⟨hgL, hg⟩
      refine ⟨hgL, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact Subgroup.mem_centralizer_iff.1 hg y (SetLike.mem_coe.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
    · rintro ⟨hgL, hg⟩
      refine ⟨hgL, ?_⟩
      have hyg : y * g = g * y := Subgroup.mem_centralizer_iff.1 hg y (Set.mem_singleton _)
      have hx' : x ∈ Subgroup.centralizer ({g} : Set G) := Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (hxL g hgL).symm
      have hy' : y ∈ Subgroup.centralizer ({g} : Set G) := Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hyg.symm
      have hle : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ≤ Subgroup.centralizer ({g} : Set G) :=
        sup_le (Subgroup.zpowers_le.2 hx') (Subgroup.zpowers_le.2 hy')
      refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
      exact (Subgroup.mem_centralizer_iff.1 (hle (SetLike.mem_coe.1 hs)) g (Set.mem_singleton _)).symm
  have hyyK : yK ^ p = 1 := hyK_pow
  have hyP : IsPGroup p (Subgroup.zpowers yK) := isPGroup_zpowers_of_pow hyyK
  obtain ⟨JK, hJK, hmapJH, huniqK, hlayK⟩ := exists_choice_component hp yK hyP JH hJH hJHu
  subst hmapJH
  have hJKle : JK ≤ Subgroup.centralizer ({yK} : Set ↥L) := hJK.1
  have hX : L ⊓ Subgroup.centralizer ({y} : Set G) = (Subgroup.centralizer ({yK} : Set ↥L)).map L.subtype :=
    (map_subtype_centralizer yK).symm
  have hJG_comp : GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) (JK.map L.subtype) := by
    rw [hX]
    exact component_map_subtype hp hJK
  have hJG_uniq : ∀ T : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer ({y} : Set G)) T →
      T = JK.map L.subtype := by
    intro T hT
    rw [hX] at hT
    obtain ⟨S, hS, hST⟩ := component_lift hp L.subtype (fun A => coprime_ker_subtype L A) _ hT
    rw [← hST, huniqK S hS]
  have hJG_layer : GLAPLayer p (L ⊓ Subgroup.centralizer ({y} : Set G)) = JK.map L.subtype :=
    layer_eq_of_unique hJG_comp hJG_uniq
  have hD_comp : GLAPComponent p (L ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) (JK.map L.subtype) := by
    rw [hD_eq]
    exact hJG_comp
  have hD_layer : GLAPLayer p (L ⊓ Subgroup.centralizer
      ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G)) = JK.map L.subtype := by
    rw [hD_eq]
    exact hJG_layer
  have hcomm_y : ∀ g ∈ JK.map L.subtype, y * g = g * y := by
    intro g hg
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
    have hk' : yK * k = k * yK := Subgroup.mem_centralizer_iff.1 (hJKle hk) yK (Set.mem_singleton _)
    exact congrArg Subtype.val hk'
  have hxJG : CentMod p (JK.map L.subtype) x := centMod_of_commute fun j hj => by
    obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hj
    exact hxL _ k.2
  have hyJG : CentMod p (JK.map L.subtype) y := centMod_of_commute hcomm_y
  have hcentD : ∀ b ∈ B, CentMod p (JK.map L.subtype) b ↔
      b ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
    intro b hb
    constructor
    · intro hCM
      have hbN : b ∈ Subgroup.normalizer (L : Set G) := hBL hb
      have hpow : (alphaHom p L ⟨b, hbN⟩) ^ p = 1 := by
        rw [← map_pow]
        have h1 : (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
          Subtype.ext (by simpa using hBel.2 b hb)
        rw [h1, map_one]
      obtain ⟨k, hk⟩ := hαfact (alphaHom p L ⟨b, hbN⟩) hpow (centMod_to_alpha hp hbN hCM)
      have hk' : alphaPQ p L b hbN = MulAut.conj (QuotientGroup.mk' (GLAPPrimeCore p ↥L) (yK ^ k)) := by
        rw [map_zpow]
        exact hk
      have hcmw := centMod_of_alpha_conj hbN (yK ^ k) hk'
      have hwy : ((yK ^ k : ↥L) : G) = y ^ k := by
        rw [SubgroupClass.coe_zpow]
      have hwB : ((yK ^ k : ↥L) : G) ∈ B := by
        rw [hwy]
        exact B.zpow_mem hyB k
      have hb' : ((yK ^ k : ↥L) : G)⁻¹ * b ∈ B := B.mul_mem (B.inv_mem hwB) hb
      have hmem := (hcm _ hb').1 hcmw
      have hwD : ((yK ^ k : ↥L) : G) ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
        rw [hwy]
        exact (le_sup_right : Subgroup.zpowers y ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers y)
          ((Subgroup.zpowers y).zpow_mem (Subgroup.mem_zpowers y) k)
      have hfin : b = ((yK ^ k : ↥L) : G) * (((yK ^ k : ↥L) : G)⁻¹ * b) := by group
      rw [hfin]
      exact (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G).mul_mem hwD
        ((le_sup_left : Subgroup.zpowers x ≤ Subgroup.zpowers x ⊔ Subgroup.zpowers y) hmem)
    · intro hbD
      have hD_le : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ≤
          centModSubgroup p (JK.map L.subtype) :=
        sup_le (Subgroup.zpowers_le.2 (centMod_iff.1 hxJG)) (Subgroup.zpowers_le.2 (centMod_iff.1 hyJG))
      exact centMod_iff.2 (hD_le hbD)
  have hzcomm : ∀ a ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G), z * a = a * z :=
    fun a ha => isElemAbelian_commute hBel hzB (hDB ha)
  have hnormz : Subgroup.zpowers z ≤
      Subgroup.normalizer ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 (normalizer_of_commute hzcomm)
  have hzcard : Nat.card (Subgroup.zpowers z) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hzp hz1
  have hzD_not : z ∉ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) := by
    intro hzD
    have hzD' : z ∈ ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := hzD
    rw [hset] at hzD'
    obtain ⟨a, ha, c, hc, hac⟩ := Set.mem_mul.1 hzD'
    have hcL : c ∈ L := (Subgroup.zpowers_le.2 hyL) hc
    have haL : a ∈ L := by
      have e : a = z * c⁻¹ := by
        rw [← hac]
        group
      rw [e]
      exact L.mul_mem hzL (L.inv_mem hcL)
    have ha1 : a = 1 := by
      have hm : a ∈ Subgroup.zpowers x ⊓ L := Subgroup.mem_inf.2 ⟨ha, haL⟩
      rw [hxL1] at hm
      exact Subgroup.mem_bot.1 hm
    have hzc : z = c := by
      rw [← hac, ha1, one_mul]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hc
    apply hzzD
    have hzK_eq : zK = yK ^ j := Subtype.ext (by
      rw [SubgroupClass.coe_zpow]
      exact hzc.trans hj.symm)
    rw [hzK_eq, map_zpow]
    exact (Subgroup.zpowers _).zpow_mem (Subgroup.mem_zpowers _) j
  have hinf : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊓ Subgroup.zpowers z = ⊥ := by
    by_contra hne
    have hdvd := Subgroup.card_dvd_of_le
      (inf_le_right : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊓ Subgroup.zpowers z ≤
        Subgroup.zpowers z)
    rw [hzcard] at hdvd
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact hne (Subgroup.eq_bot_of_card_eq _ h1)
    · have heq : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊓ Subgroup.zpowers z =
          Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hzcard, h1])
      have hzmem : z ∈ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) := by
        have hz_mem : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
        rw [← heq] at hz_mem
        exact (Subgroup.mem_inf.1 hz_mem).1
      exact hzD_not hzmem
  have hEcard : Nat.card ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊔ Subgroup.zpowers z :
      Subgroup G) = p ^ 3 := by
    have h := card_sup_mul_card_inf_of_le_normalizer hnormz
    rw [hinf, Subgroup.card_bot, mul_one, hDcard, hzcard] at h
    rw [h]
    ring
  have hEB : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊔ Subgroup.zpowers z ≤ B :=
    sup_le hDB (Subgroup.zpowers_le.2 hzB)
  have hEel : IsElemAbelian p ((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊔
      Subgroup.zpowers z : Subgroup G) :=
    isElemAbelian_mono hBel hEB
  have hDE : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ≤
      (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊔ Subgroup.zpowers z := le_sup_left
  have hzC : zK ∈ Subgroup.centralizer ({yK} : Set ↥L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    apply Subtype.ext
    exact isElemAbelian_commute hBel hyB hzB
  have hzN : zK ∈ Subgroup.normalizer ((JK : Subgroup ↥L) : Set ↥L) :=
    le_normalizer_of_unique_glaPComponent hJK huniqK hzC
  have hzP : IsPGroup p (Subgroup.zpowers zK) := isPGroup_zpowers_of_pow hzK_pow
  have hK_layer : GLAPLayer p (JK ⊓ Subgroup.centralizer ({zK} : Set ↥L)) ≠ ⊥ := by
    obtain ⟨M, hM⟩ := exists_component_of_layer_ne_bot hzzL
    rw [← map_inf_centralizer_eq hp (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) (coprime_inf_quot hp L) hzP hzN]
      at hM
    obtain ⟨S, hS, -⟩ := component_lift hp (QuotientGroup.mk' (GLAPPrimeCore p ↥L))
      (coprime_inf_quot hp L) _ hM
    exact layer_ne_bot_of_component hS
  have hlayG : GLAPLayer p ((JK ⊓ Subgroup.centralizer ({zK} : Set ↥L)).map L.subtype) ≠ ⊥ := by
    obtain ⟨S, hS⟩ := exists_component_of_layer_ne_bot hK_layer
    exact layer_ne_bot_of_component (component_map_subtype hp hS)
  have hmapz : (JK ⊓ Subgroup.centralizer ({zK} : Set ↥L)).map L.subtype =
      JK.map L.subtype ⊓ Subgroup.centralizer ({z} : Set G) := by
    ext g
    constructor
    · rintro ⟨k, ⟨hkJ, hkC⟩, rfl⟩
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨k, hkJ, rfl⟩,
        Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hk' : zK * k = k * zK := Subgroup.mem_centralizer_iff.1 hkC zK (Set.mem_singleton _)
      exact congrArg Subtype.val hk'
    · intro hg
      obtain ⟨hgJ, hgC⟩ := Subgroup.mem_inf.1 hg
      obtain ⟨k, hkJ, rfl⟩ := Subgroup.mem_map.1 hgJ
      refine ⟨k, ⟨hkJ, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩, rfl⟩
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.1 hgC z (Set.mem_singleton _)
  have hEJ : JK.map L.subtype ⊓ Subgroup.centralizer
      (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊔ Subgroup.zpowers z : Subgroup G) : Set G) =
        JK.map L.subtype ⊓ Subgroup.centralizer ({z} : Set G) := by
    ext g
    constructor
    · rintro ⟨hgJ, hgE⟩
      refine Subgroup.mem_inf.2 ⟨hgJ, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact Subgroup.mem_centralizer_iff.1 hgE z (SetLike.mem_coe.2
        ((le_sup_right : Subgroup.zpowers z ≤ (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊔
          Subgroup.zpowers z) (Subgroup.mem_zpowers z)))
    · intro hg
      obtain ⟨hgJ, hgz⟩ := Subgroup.mem_inf.1 hg
      have hgL : g ∈ L := by
        obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hgJ
        exact k.2
      have hx' : x ∈ Subgroup.centralizer ({g} : Set G) := Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (hxL g hgL).symm
      have hy' : y ∈ Subgroup.centralizer ({g} : Set G) := Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (hcomm_y g hgJ).symm
      have hz' : z ∈ Subgroup.centralizer ({g} : Set G) := Subgroup.mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact (Subgroup.mem_centralizer_iff.1 hgz z (Set.mem_singleton _)).symm
      have hle : (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊔ Subgroup.zpowers z ≤
          Subgroup.centralizer ({g} : Set G) :=
        sup_le (sup_le (Subgroup.zpowers_le.2 hx') (Subgroup.zpowers_le.2 hy')) (Subgroup.zpowers_le.2 hz')
      refine Subgroup.mem_inf.2 ⟨hgJ, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 (hle (SetLike.mem_coe.1 hs)) g (Set.mem_singleton _)).symm
  have hlayE : GLAPLayer p (JK.map L.subtype ⊓ Subgroup.centralizer
      (((Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊔ Subgroup.zpowers z : Subgroup G) : Set G)) ≠ ⊥ := by
    rw [hEJ, ← hmapz]
    exact hlayG
  have e : PQuot p (JK.map L.subtype) ≃* PQuot p (JK.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L))) :=
    (lcEquiv hp L.subtype JK (coprime_ker_subtype L JK)).symm.trans
      (lcEquiv hp (QuotientGroup.mk' (GLAPPrimeCore p ↥L)) JK (coprime_inf_quot hp L JK))
  exact ⟨y, hyBL, hy1, JK.map L.subtype, (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) ⊔
    Subgroup.zpowers z, hD_layer, hD_comp, hcentD, hEB, hEel, hEcard, hDE, hlayE,
    JK.map (QuotientGroup.mk' (GLAPPrimeCore p ↥L)), hJT, ⟨e⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.H81
