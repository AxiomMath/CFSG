module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55R3
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55FTGQuot
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Simple
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87BadSL3

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

namespace EL3

open Subgroup CFSG CFSG.LocalCores CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem kindFactorAll_of_le_centralizer (hInv : InvSec) {G : Type} [Group G] [Finite G] {z : G}
    {k : Kind} {S : Subgroup G} (hctx : Stage2Ctx G z k S) (H : Subgroup G)
    {J : Subgroup (HBar H)} (hJ : IsComponent J) {u : HBar H} (hu2 : orderOf u = 2)
    (hJC : J ≤ centralizer ({u} : Set (HBar H))) : KindFactorAll k (↥J ⧸ center ↥J) := by
  have hs : IsSimpleGroup (↥J ⧸ center ↥J) := hJ.1.2.1
  have hns : ¬ Group.IsSolvable (↥J ⧸ center ↥J) := by
    intro hsol
    obtain ⟨a, b, hab⟩ := hJ.1.2.2
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hsol a b)
  have hsec : IsSection (↥J ⧸ center ↥J) ↥J :=
    ⟨⊤, (QuotientGroup.mk' (center ↥J)).comp (⊤ : Subgroup ↥J).subtype, fun v => by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective v
      exact ⟨⟨w, Subgroup.mem_top w⟩, rfl⟩⟩
  exact hbar_invsec hInv hctx H u hu2 _ hns (IsSection.of_le_le hJC hsec)

theorem normal_of_odd_centralizer {A : Type} [Group A] [Finite A] {J : Subgroup A}
    (hJ : IsComponent J) (hodd : ¬ 2 ∣ Nat.card ↥(centralizer (J : Set A))) : J.Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hJ' : IsComponent (J.map (MulAut.conj g).toMonoidHom) :=
    isComponent_map_mulEquiv (MulAut.conj g) hJ
  rcases distinct_components_commute hJ' hJ with heq | hbot
  · have hmem : g * n * g⁻¹ ∈ J.map (MulAut.conj g).toMonoidHom := ⟨n, hn, MulAut.conj_apply g n⟩
    rwa [heq] at hmem
  · exfalso
    have hle : J.map (MulAut.conj g).toMonoidHom ≤ centralizer (J : Set A) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hev : ¬ Odd (Nat.card ↥(J.map (MulAut.conj g).toMonoidHom)) :=
      FTG.not_odd_card_of_isQuasisimple hJ'.1
    have hd := Subgroup.card_dvd_of_le hle
    exact hodd (dvd_trans (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hev)) hd)

theorem normal_centralizer_of_normal {A : Type} [Group A] {J : Subgroup A} [hJ : J.Normal] :
    (centralizer (J : Set A)).Normal := by
  refine ⟨fun c hc g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro j hj
  have hj' : g⁻¹ * j * g ∈ J := by simpa using hJ.conj_mem j hj g⁻¹
  have h1 := hc _ hj'
  calc j * (g * c * g⁻¹) = g * ((g⁻¹ * j * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * j * g)) * g⁻¹ := by rw [h1]
    _ = (g * c * g⁻¹) * j := by group

theorem hbarComp_of_bad (hInv : InvSec) {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (hctx : Stage2Ctx G z k S) (H : Subgroup G) {J : Subgroup (HBar H)}
    (hJ : IsComponent J) (hbad : ¬ KindFactorAll k (↥J ⧸ center ↥J)) :
    J.Normal ∧ centralizer (J : Set (HBar H)) = ⊥ ∧
      ∀ u : HBar H, orderOf u = 2 → ¬ J ≤ centralizer ({u} : Set (HBar H)) := by
  have hno : ∀ u : HBar H, orderOf u = 2 → ¬ J ≤ centralizer ({u} : Set (HBar H)) :=
    fun u hu hJC => hbad (kindFactorAll_of_le_centralizer hInv hctx H hJ hu hJC)
  have hodd : ¬ 2 ∣ Nat.card ↥(centralizer (J : Set (HBar H))) := by
    intro h2
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hu2 : orderOf (x : HBar H) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    refine hno (x : HBar H) hu2 fun j hj => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp x.2 j hj
  have hnorm : J.Normal := normal_of_odd_centralizer hJ hodd
  refine ⟨hnorm, ?_, hno⟩
  have hCn : (centralizer (J : Set (HBar H))).Normal := normal_centralizer_of_normal
  have hle : centralizer (J : Set (HBar H)) ≤ pPrimeCore 2 (HBar H) :=
    le_sSup ⟨hCn, (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd⟩
  have hbot : pPrimeCore 2 (HBar H) = ⊥ :=
    _root_.CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot (G := ↥H) 2
  exact le_bot_iff.mp (hbot ▸ hle)

theorem center_eq_bot_of_centralizer_eq_bot {A : Type} [Group A] {J : Subgroup A}
    (h : centralizer (J : Set A) = ⊥) : center ↥J = ⊥ := by
  refine eq_bot_iff.mpr fun z hz => ?_
  have hz' : (z : A) ∈ centralizer (J : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨j, hj⟩)
  rw [h, Subgroup.mem_bot] at hz'
  exact Subgroup.mem_bot.mpr (Subtype.ext hz')

theorem kindFactorAll_of_equiv {k : Kind} {Y T : Type} [Group Y] [Group T] (e : Y ≃* T)
    (h : KindFactorAll k Y) : KindFactorAll k T := by
  have hL2 : IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) → IVK.IsL2 T (fun r => Odd r ∧ 5 ≤ r) := by
    rintro ⟨F, hF, hFin, hP, ⟨f⟩⟩
    exact ⟨F, hF, hFin, hP, ⟨e.symm.trans f⟩⟩
  have hSec : ∀ {B : Type} [Group B], IsSection Y B → IsSection T B := by
    rintro B _ ⟨U, φ, hφ⟩
    exact ⟨U, e.toMonoidHom.comp φ, e.surjective.comp hφ⟩
  cases k with
  | g2 => exact hL2 h
  | psp4 => exact hL2 h
  | m12 => exact hL2 h
  | l4 ε =>
    rcases h with h | h
    · exact Or.inl (hL2 h)
    · exact Or.inr (hSec h)
  | mcl =>
    obtain ⟨n, h1, h2, h3⟩ := h
    exact ⟨n, h1, h2, hSec h3⟩
  | ly =>
    obtain ⟨n, h1, h2, h3⟩ := h
    exact ⟨n, h1, h2, hSec h3⟩

theorem l3_not_kindFactorAll (k : Kind) {Y : Type} [Group Y] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (hodd : Odd (p ^ f)) (hL : CFSG.Blueprint.LieModel Y .PSL 3 p f) :
    ¬ KindFactorAll k Y := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hL
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hFodd : Odd (Nat.card F) := hcard ▸ hodd
  have h3 : 3 ≤ Nat.card F := by
    have h2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    have := Nat.odd_iff.mp hodd
    rw [hcard]
    omega
  intro h
  exact not_kindFactorAll hp2 (involved_qdSL_projectiveSL3 (p := p))
    (not_card_dvd_factorial_projectiveSL3 hFodd h3) (kindFactorAll_of_equiv e h)

end EL3

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
