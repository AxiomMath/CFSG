module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem l94t_mem_core_iff {p : ℕ} {X : Subgroup G} (u : ↥X) :
    u ∈ GLAPPrimeCore p ↥X ↔ (u : G) ∈ GLAPPrimeCoreOf p X := by
  constructor
  · intro h
    exact Subgroup.mem_map.2 ⟨u, h, rfl⟩
  · intro h
    obtain ⟨z, hz, hzu⟩ := Subgroup.mem_map.1 h
    have hzeq : z = u := Subtype.ext hzu
    rw [← hzeq]
    exact hz

theorem l94t_mk_eq_one_iff {p : ℕ} {X : Subgroup G} {a : G} (ha : a ∈ X) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨a, ha⟩ : ↥X) = 1 ↔ a ∈ GLAPPrimeCoreOf p X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact l94t_mem_core_iff (p := p) (⟨a, ha⟩ : ↥X)

theorem l94t_mk_comm_iff {p : ℕ} {X : Subgroup G} {a b : G} (ha : a ∈ X) (hb : b ∈ X) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨a, ha⟩ : ↥X) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨b, hb⟩ : ↥X) =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨b, hb⟩ : ↥X) *
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨a, ha⟩ : ↥X) ↔
      ⁅a, b⁆ ∈ GLAPPrimeCoreOf p X := by
  have hc : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⁅(⟨a, ha⟩ : ↥X), ⟨b, hb⟩⁆) =
      ⁅QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨a, ha⟩ : ↥X),
        QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨b, hb⟩ : ↥X)⁆ :=
    map_commutatorElement _ _ _
  have key : QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⁅(⟨a, ha⟩ : ↥X), ⟨b, hb⟩⁆) = 1 ↔
      ⁅a, b⁆ ∈ GLAPPrimeCoreOf p X := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact l94t_mem_core_iff (p := p) _
  rw [← commutatorElement_eq_one_iff_mul_comm, ← hc, key]

theorem l94t_conj_mem_O {p : ℕ} {X : Subgroup G} {g o : G} (hg : g ∈ X)
    (ho : o ∈ GLAPPrimeCoreOf p X) : g * o * g⁻¹ ∈ GLAPPrimeCoreOf p X := by
  obtain ⟨z, hz, hzo⟩ := Subgroup.mem_map.1 ho
  refine Subgroup.mem_map.2 ⟨(⟨g, hg⟩ : ↥X) * z * (⟨g, hg⟩ : ↥X)⁻¹,
    Subgroup.Normal.conj_mem inferInstance z hz _, ?_⟩
  rw [← hzo]
  simp

theorem l94t_card_barX {p : ℕ} {X S : Subgroup G} (hSX : S ≤ X)
    (hSO : S ⊓ GLAPPrimeCoreOf p X = ⊥) :
    Nat.card (barX p X S) = Nat.card S := by
  classical
  let ψ : ↥(S.subgroupOf X) →* (↥X ⧸ GLAPPrimeCore p ↥X) :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥X)).comp (S.subgroupOf X).subtype
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).2 fun z hz => ?_
    have hz' : ((z : ↥X) : G) ∈ GLAPPrimeCoreOf p X :=
      (l94t_mk_eq_one_iff (p := p) (z : ↥X).2).1 hz
    have hmem : ((z : ↥X) : G) ∈ S ⊓ GLAPPrimeCoreOf p X :=
      ⟨Subgroup.mem_subgroupOf.1 z.2, hz'⟩
    rw [hSO, Subgroup.mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  have hmap : barX p X S = (⊤ : Subgroup ↥(S.subgroupOf X)).map ψ := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    · rintro ⟨z, -, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
  rw [hmap, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv

theorem l94t_isElemAbelian_map {A B : Type} [Group A] [Group B] {p : ℕ} (f : A →* B)
    {E : Subgroup A} (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxa, ← hyb, ← map_mul, ← map_mul,
      isElemAbelian_commute hE hx hy]
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hz
    rw [← map_pow, hE.2 x hx, map_one]

theorem l94t_isElemAbelian_barX {p : ℕ} {X S : Subgroup G} (hS : IsElemAbelian p S)
    (hSX : S ≤ X) : IsElemAbelian p (barX p X S) := by
  have hE : IsElemAbelian p (S.subgroupOf X) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => ?_⟩
    · exact isElemAbelian_commute hS (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)
    · refine Subtype.ext ?_
      simpa using hS.2 _ (Subgroup.mem_subgroupOf.1 ha)
  exact l94t_isElemAbelian_map _ hE

theorem l94t_mem_normalizer_barX {p : ℕ} {X S : Subgroup G} (hSX : S ≤ X) {a : G} (ha : a ∈ X)
    (haS : a ∈ Subgroup.normalizer (S : Set G)) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨a, ha⟩ : ↥X) ∈
      Subgroup.normalizer ((barX p X S : Subgroup _) : Set _) := by
  have h1 : (⟨a, ha⟩ : ↥X) ∈ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro v
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.1 haS (v : G)
    exact this
  have h2 := Subgroup.le_normalizer_map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))
    (Subgroup.mem_map_of_mem _ h1)
  exact h2

theorem l94t_barX_le_normalizer {p : ℕ} {X S A : Subgroup G} (hSX : S ≤ X)
    (hA : A ≤ Subgroup.normalizer (S : Set G)) :
    barX p X A ≤ Subgroup.normalizer ((barX p X S : Subgroup _) : Set _) := by
  rintro _ ⟨w, hw, rfl⟩
  exact l94t_mem_normalizer_barX (p := p) hSX w.2 (hA (Subgroup.mem_subgroupOf.1 hw))

theorem l94t_central_mk {p : ℕ} {X : Subgroup G} {x : G} (hx : x ∈ X)
    (hxc : ∀ w ∈ X, w * x = x * w) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) (⟨x, hx⟩ : ↥X) ∈
      Subgroup.center (↥X ⧸ GLAPPrimeCore p ↥X) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥X) g
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hxc w w.2)

theorem l94t_barX_ne_bot {X S : Subgroup G} (hSX : S ≤ X) (hS2 : IsPGroup 2 S) (hSne : S ≠ ⊥)
    (hodd : Odd (Nat.card (GLAPPrimeCoreOf 3 X))) : barX 3 X S ≠ ⊥ := by
  intro hbot
  have hSO : S ≤ GLAPPrimeCoreOf 3 X := by
    intro s hs
    have hmem : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨s, hSX hs⟩ : ↥X) ∈ barX 3 X S :=
      ⟨⟨s, hSX hs⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (l94t_mk_eq_one_iff (p := 3) (hSX hs)).1 hmem
  apply hSne
  rcases hS2.card_eq_or_dvd with h1 | h2
  · exact Subgroup.card_eq_one.1 h1
  · exact absurd (even_iff_two_dvd.2 (h2.trans (Subgroup.card_dvd_of_le hSO)))
      (Nat.not_even_iff_odd.2 hodd)

theorem l94t_isPGroup_barX {p q : ℕ} {X S : Subgroup G} (hSX : S ≤ X) (hS : IsPGroup q S) :
    IsPGroup q (barX p X S) := by
  intro g
  obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.1 g.2
  obtain ⟨n, hn⟩ := hS ⟨(w : G), Subgroup.mem_subgroupOf.1 hw⟩
  refine ⟨n, Subtype.ext ?_⟩
  have hw1 : (w : G) ^ q ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hwq : w ^ q ^ n = (1 : ↥X) := Subtype.ext (by simpa using hw1)
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hwg, ← map_pow, hwq, map_one]

theorem l94t_transport_hy {Y Q : Type*} [Group Y] [Group Q] {K : Subgroup Q}
    (e : Y ≃* ↥K)
    (hy : ∃ y : Y, orderOf y = 3 ∧ ∃ W : Subgroup Y, IsPGroup 2 W ∧ W ≠ ⊥ ∧
      y ∈ Subgroup.normalizer (W : Set Y)) :
    ∃ y ∈ K, orderOf y = 3 ∧ ∃ W : Subgroup Q, W ≤ K ∧ IsPGroup 2 W ∧ W ≠ ⊥ ∧
      y ∈ Subgroup.normalizer (W : Set Q) := by
  obtain ⟨y, hy3, W, hW2, hWne, hyW⟩ := hy
  refine ⟨(e y : Q), (e y).2, ?_, (W.map e.toMonoidHom).map K.subtype,
    Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · have h1 : orderOf (e y) = orderOf y := orderOf_injective e.toMonoidHom e.injective y
    have h2 : orderOf (K.subtype (e y)) = orderOf (e y) :=
      orderOf_injective K.subtype K.subtype_injective (e y)
    show orderOf (K.subtype (e y)) = 3
    rw [h2, h1, hy3]
  · exact (hW2.map e.toMonoidHom).map K.subtype
  · intro h0
    apply hWne
    have h1 := (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h0
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h1
  · have h1 : e.toMonoidHom y ∈ Subgroup.normalizer ((W.map e.toMonoidHom : Subgroup ↥K) : Set ↥K) :=
      Subgroup.le_normalizer_map e.toMonoidHom (Subgroup.mem_map_of_mem _ hyW)
    exact Subgroup.le_normalizer_map K.subtype (Subgroup.mem_map_of_mem _ h1)

theorem l94t_isSimple_barX {p : ℕ} (hp : p.Prime) {X L : Subgroup G} (hLX : L ≤ X)
    (hLsn : IsSubnormal L X) (hZ : Subgroup.center (PQuot p L) = ⊥)
    (hq : CFSG.Open.IsQuasisimple (PQuot p L)) : IsSimpleGroup ↥(barX p X L) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsP : IsSimpleGroup (PQuot p L) := by
    have e0 : (PQuot p L ⧸ Subgroup.center (PQuot p L)) ≃* PQuot p L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    haveI : IsSimpleGroup (PQuot p L ⧸ Subgroup.center (PQuot p L)) := hq.2
    exact e0.symm.isSimpleGroup
  exact (quotEquivBarX hp hLX hLsn).symm.isSimpleGroup

theorem l94t_x_not_mem_L {B L : Subgroup G} {x : G} (h : H92 3 B x L)
    (hZ : Subgroup.center (PQuot 3 L) = ⊥) : x ∉ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hxL
  have hBel : IsElemAbelian 3 B := h.bmax.1
  have hx3 : orderOf x = 3 := orderOf_eq_prime (hBel.2 x h.mem) h.ne_one
  have hcen : QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) (⟨x, hxL⟩ : ↥L) ∈
      Subgroup.center (PQuot 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (h.comp.1 w.2))
  rw [hZ, Subgroup.mem_bot] at hcen
  have hxO : x ∈ GLAPPrimeCoreOf 3 L := (l94t_mk_eq_one_iff (p := 3) hxL).1 hcen
  have hdvd := Subgroup.orderOf_dvd_natCard _ hxO
  rw [hx3] at hdvd
  exact not_dvd_card_glaPPrimeCoreOf (p := 3) Nat.prime_three L hdvd


theorem l94t_sup_eq_preimBarX {L X : Subgroup G} (hLX : L ≤ X) :
    L ⊔ GLAPPrimeCoreOf 3 X = preimBarX 3 X L := by
  apply le_antisymm
  · refine sup_le (le_preimBarX 3 hLX) ?_
    intro o ho
    have hoX : o ∈ X := Subgroup.map_subtype_le _ ho
    refine Subgroup.mem_map.2 ⟨⟨o, hoX⟩, Subgroup.mem_comap.2 ?_, rfl⟩
    rw [(l94t_mk_eq_one_iff (p := 3) hoX).2 ho]
    exact Subgroup.one_mem _
  · intro g hg
    obtain ⟨k, hk, hkg⟩ := exists_mul_of_mem_preimBarX 3 hg
    have e : g = k * (k⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hk hkg

theorem l94t_barX_le_sup_centralizer {B L : Subgroup G} {x : G} (h : H92 3 B x L)
    (hin : ∀ b ∈ B, InducesInnerMod 3 L b) :
    barX 3 (cx x) B ≤ barX 3 (cx x) L ⊔
      Subgroup.centralizer ((barX 3 (cx x) L : Subgroup _) : Set _) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hBX : B ≤ cx x := isElemAbelian_le_centralizer h.bmax.1 h.mem
  have hLX : L ≤ cx x := h.comp.1
  have hLsn : IsSubnormal L (cx x) := h.comp.2.1
  have hO : GLAPPrimeCoreOf 3 L ≤ GLAPPrimeCoreOf 3 (cx x) :=
    glaPPrimeCoreOf_le_of_isSubnormal hp3 hLsn
  rintro _ ⟨w, hw, rfl⟩
  have hb : (w : G) ∈ B := Subgroup.mem_subgroupOf.1 hw
  obtain ⟨l, hl, hlin⟩ := hin _ hb
  have hlX : l ∈ cx x := hLX hl
  have hbX : (w : G) ∈ cx x := hBX hb
  have hcX : (w : G) * l⁻¹ ∈ cx x := (cx x).mul_mem hbX ((cx x).inv_mem hlX)
  have hbinv : ∀ y ∈ L, (w : G)⁻¹ * y * (w : G) ∈ L := by
    intro y hy
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (h.norm hb)) y).1 hy
    rwa [inv_inv] at this
  have hcomm : ∀ y ∈ L, ⁅y, (w : G) * l⁻¹⁆ ∈ GLAPPrimeCoreOf 3 (cx x) := by
    intro y hy
    obtain ⟨o₁, ho₁⟩ : ∃ o₁ : G, o₁ = (l⁻¹ * y * l)⁻¹ * ((w : G)⁻¹ * y * (w : G)) := ⟨_, rfl⟩
    have ho₁L : o₁ ∈ GLAPPrimeCoreOf 3 L := by
      rw [ho₁]
      exact hlin y hy
    have ho₁O : o₁ ∈ GLAPPrimeCoreOf 3 (cx x) := hO ho₁L
    have hu : (w : G)⁻¹ * y * (w : G) = (l⁻¹ * y * l) * o₁ := by
      rw [ho₁]
      group
    obtain ⟨o, ho⟩ : ∃ o : G, o = l * o₁ * l⁻¹ := ⟨_, rfl⟩
    have hoO : o ∈ GLAPPrimeCoreOf 3 (cx x) := by
      rw [ho]
      exact l94t_conj_mem_O hlX ho₁O
    have hco : ((w : G) * l⁻¹)⁻¹ * y * ((w : G) * l⁻¹) = y * o := by
      calc ((w : G) * l⁻¹)⁻¹ * y * ((w : G) * l⁻¹) = l * ((w : G)⁻¹ * y * (w : G)) * l⁻¹ := by
            group
        _ = l * ((l⁻¹ * y * l) * o₁) * l⁻¹ := by rw [hu]
        _ = y * o := by rw [ho]; group
    have hyc : y * ((w : G) * l⁻¹) = ((w : G) * l⁻¹) * (y * o) := by
      rw [← hco]
      group
    have hcm : ⁅y, (w : G) * l⁻¹⁆ = ((w : G) * l⁻¹) * (y * o * y⁻¹) * ((w : G) * l⁻¹)⁻¹ := by
      rw [commutatorElement_def, hyc]
      group
    rw [hcm]
    exact l94t_conj_mem_O hcX (l94t_conj_mem_O (hLX hy) hoO)
  have hC : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) (⟨(w : G) * l⁻¹, hcX⟩ : ↥(cx x)) ∈
      Subgroup.centralizer ((barX 3 (cx x) L : Subgroup _) : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro k hk
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hk
    have hvL : (v : G) ∈ L := Subgroup.mem_subgroupOf.1 hv
    exact (l94t_mk_comm_iff (p := 3) (hLX hvL) hcX).2 (hcomm v hvL)
  have hl' : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) (⟨l, hlX⟩ : ↥(cx x)) ∈
      barX 3 (cx x) L :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hl)
  have hdec : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) w =
      QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) (⟨(w : G) * l⁻¹, hcX⟩ : ↥(cx x)) *
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) (⟨l, hlX⟩ : ↥(cx x)) := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext (by simp)
  rw [sup_comm, hdec]
  exact Subgroup.mul_mem_sup hC hl'


theorem l94t_barX_inter_centralizer {B L : Subgroup G} {x : G} (h : H92 3 B x L) :
    barX 3 (cx x) B ⊓ Subgroup.centralizer ((barX 3 (cx x) L : Subgroup _) : Set _) =
      Subgroup.zpowers (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) (⟨x, Subgroup.mem_centralizer_singleton_iff.2 (Commute.refl x)⟩ : ↥(cx x))) := by
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hBel : IsElemAbelian 3 B := h.bmax.1
  have hBX : B ≤ cx x := isElemAbelian_le_centralizer hBel h.mem
  have hLX : L ≤ cx x := h.comp.1
  have hLsn : IsSubnormal L (cx x) := h.comp.2.1
  have hxX : x ∈ cx x := Subgroup.mem_centralizer_singleton_iff.2 (Commute.refl x)
  have hLO : L ⊓ GLAPPrimeCoreOf 3 (cx x) = GLAPPrimeCoreOf 3 L :=
    glaPPrimeCoreOf_inf_eq_of_isSubnormal hp3 hLsn
  have hxc : ∀ w ∈ cx x, w * x = x * w := fun w hw => Subgroup.mem_centralizer_singleton_iff.1 hw
  have hcen : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) (⟨x, hxX⟩ : ↥(cx x)) ∈
      Subgroup.center (↥(cx x) ⧸ GLAPPrimeCore 3 ↥(cx x)) := l94t_central_mk hxX hxc
  ext z
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hzB, hzC⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hzB
    have hb : (w : G) ∈ B := Subgroup.mem_subgroupOf.1 hw
    have hpt : ∀ l ∈ L, ⁅l, (w : G)⁆ ∈ GLAPPrimeCoreOf 3 L := by
      intro l hl
      have hmemK : QuotientGroup.mk' (GLAPPrimeCore 3 ↥(cx x)) (⟨l, hLX hl⟩ : ↥(cx x)) ∈
          barX 3 (cx x) L := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hl)
      have hcomm := (l94t_mk_comm_iff (p := 3) (hLX hl) w.2).1
        (Subgroup.mem_centralizer_iff.1 hzC _ hmemK)
      have hOc : ⁅l, (w : G)⁆ ∈ GLAPPrimeCoreOf 3 (cx x) := hcomm
      have hLc : ⁅l, (w : G)⁆ ∈ L := by
        have e : ⁅l, (w : G)⁆ = l * ((w : G) * l⁻¹ * (w : G)⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact L.mul_mem hl ((Subgroup.mem_normalizer_iff.1 (h.norm hb) l⁻¹).1 (L.inv_mem hl))
      have hmem : ⁅l, (w : G)⁆ ∈ L ⊓ GLAPPrimeCoreOf 3 (cx x) := Subgroup.mem_inf.2 ⟨hLc, hOc⟩
      rw [hLO] at hmem
      exact hmem
    have hcentM : CentMod 3 L (w : G) := centMod_iff.2 ⟨h.norm hb, hpt⟩
    have hbz : (w : G) ∈ Subgroup.zpowers x := (h.cent _ hb).1 hcentM
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hbz
    refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simp [hi])
  · intro hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hmemB : x ^ i ∈ B := B.zpow_mem h.mem i
    refine ⟨?_, ?_⟩
    · rw [← map_zpow]
      exact ⟨⟨x, hxX⟩ ^ i, Subgroup.mem_subgroupOf.2 (by simpa using hmemB), rfl⟩
    · have hzc := Subgroup.zpow_mem _ hcen i
      rw [Subgroup.mem_centralizer_iff]
      intro k _
      exact Subgroup.mem_center_iff.1 hzc k

theorem l94t_commutator_facts {B T₀ : Subgroup G} (hBel : IsElemAbelian 3 B)
    (hT₀2 : IsPGroup 2 T₀) (hBT₀ : B ≤ Subgroup.normalizer (T₀ : Set G)) :
    ⁅T₀, B⁆ ≤ T₀ ∧ IsPGroup 2 (⁅T₀, B⁆ : Subgroup G) ∧
      B ≤ Subgroup.normalizer ((⁅T₀, B⁆ : Subgroup G) : Set G) ∧ ⁅⁅T₀, B⁆, B⁆ = ⁅T₀, B⁆ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : IsPGroup 3 B := isPGroup_of_isElemAbelian hBel
  have hTT₀ : ⁅T₀, B⁆ ≤ T₀ := by
    refine Subgroup.commutator_le.2 fun t ht b hb => ?_
    have e : ⁅t, b⁆ = t * (b * t⁻¹ * b⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact T₀.mul_mem ht ((Subgroup.mem_normalizer_iff.1 (hBT₀ hb) t⁻¹).1 (T₀.inv_mem ht))
  have hT2 : IsPGroup 2 ↥(⁅T₀, B⁆ : Subgroup G) := hT₀2.to_le hTT₀
  have hBnT : B ≤ Subgroup.normalizer ((⁅T₀, B⁆ : Subgroup G) : Set G) := by
    have key : ∀ b' ∈ B, ⁅T₀, B⁆ ≤ (⁅T₀, B⁆ : Subgroup G).comap (MulAut.conj b').toMonoidHom := by
      intro b' hb'
      refine Subgroup.commutator_le.2 fun t ht c hc => ?_
      rw [Subgroup.mem_comap]
      have hbc : b' * c = c * b' := isElemAbelian_commute hBel hb' hc
      have hct : (MulAut.conj b') c = c := by
        rw [MulAut.conj_apply, hbc]
        group
      show (MulAut.conj b') ⁅t, c⁆ ∈ ⁅T₀, B⁆
      rw [map_commutatorElement, hct]
      exact Subgroup.commutator_mem_commutator
        ((Subgroup.mem_normalizer_iff.1 (hBT₀ hb') t).1 ht) hc
    intro b' hb'
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact key b' hb' hy
    · intro hy
      have h1 : b'⁻¹ * (b' * y * b'⁻¹) * b'⁻¹⁻¹ ∈ ⁅T₀, B⁆ := key b'⁻¹ (B.inv_mem hb') hy
      have e : b'⁻¹ * (b' * y * b'⁻¹) * b'⁻¹⁻¹ = y := by group
      rwa [e] at h1
  have hsolv : Group.IsSolvable ↥T₀ := by
    haveI := hT₀2.isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card B) (Nat.card ↥T₀) :=
    IsPGroup.coprime_card_of_ne 3 2 (by norm_num) B T₀ hB3 hT₀2
  have hdbl : ⁅⁅T₀, B⁆, B⁆ = ⁅T₀, B⁆ := GL83.commutator_double_eq_self B T₀ hBT₀ hcop hsolv
  exact ⟨hTT₀, hT2, hBnT, hdbl⟩


end CFSG.LocalAnalysis.GLTheoremA.S9
