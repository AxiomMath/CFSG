module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD4
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzCover
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti

section Generic

variable {G : Type*} [Group G]

theorem mem_sup_exists_of_commute {H L : Subgroup G} (hc : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h)
    {x : G} (hx : x ∈ H ⊔ L) : ∃ h ∈ H, ∃ l ∈ L, h * l = x := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, L.one_mem, mul_one x⟩
    · exact ⟨1, H.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, H.one_mem, 1, L.one_mem, one_mul 1⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨h1, hh1, l1, hl1, rfl⟩ := ihx
    obtain ⟨h2, hh2, l2, hl2, rfl⟩ := ihy
    refine ⟨h1 * h2, H.mul_mem hh1 hh2, l1 * l2, L.mul_mem hl1 hl2, ?_⟩
    calc h1 * h2 * (l1 * l2) = h1 * (h2 * l1) * l2 := by group
      _ = h1 * (l1 * h2) * l2 := by rw [hc h2 hh2 l1 hl1]
      _ = h1 * l1 * (h2 * l2) := by group
  | inv x _ ih =>
    obtain ⟨h1, hh1, l1, hl1, rfl⟩ := ih
    refine ⟨h1⁻¹, H.inv_mem hh1, l1⁻¹, L.inv_mem hl1, ?_⟩
    have hc' : Commute h1 l1 := hc h1 hh1 l1 hl1
    rw [mul_inv_rev, ← (hc'.inv_inv).eq]

theorem isMulCommutative_sup_of_commute {H L : Subgroup G}
    (hH : ∀ h1 ∈ H, ∀ h2 ∈ H, h1 * h2 = h2 * h1) (hL : ∀ l1 ∈ L, ∀ l2 ∈ L, l1 * l2 = l2 * l1)
    (hc : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h) : IsMulCommutative (H ⊔ L : Subgroup G) := by
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨h1, hh1, l1, hl1, e1⟩ := mem_sup_exists_of_commute hc a.2
  obtain ⟨h2, hh2, l2, hl2, e2⟩ := mem_sup_exists_of_commute hc b.2
  apply Subtype.ext
  change a.1 * b.1 = b.1 * a.1
  rw [← e1, ← e2]
  calc h1 * l1 * (h2 * l2) = h1 * (l1 * h2) * l2 := by group
    _ = h1 * (h2 * l1) * l2 := by rw [hc h2 hh2 l1 hl1]
    _ = (h1 * h2) * (l1 * l2) := by group
    _ = (h2 * h1) * (l2 * l1) := by rw [hH h1 hh1 h2 hh2, hL l1 hl1 l2 hl2]
    _ = h2 * (h1 * l2) * l1 := by group
    _ = h2 * (l2 * h1) * l1 := by rw [hc h1 hh1 l2 hl2]
    _ = h2 * l2 * (h1 * l1) := by group

end Generic

section Center

variable {Y : Type} [Group Y] [Finite Y]

theorem isPGroup_center_of_core {K : Subgroup Y} (hcore : CFSG.pPrimeCore 3 ↥K = ⊥) :
    IsPGroup 3 (Subgroup.center ↥K) := by
  intro z
  have hwc : (z : ↥K) ∈ Subgroup.center ↥K := z.2
  have hn : orderOf (z : ↥K) ≠ 0 := (isOfFinOrder_of_finite _).orderOf_pos.ne'
  obtain ⟨a, m, hm, hwm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn 3 (by norm_num)
  set u : ↥K := (z : ↥K) ^ (3 ^ a) with hu
  have huc : u ∈ Subgroup.center ↥K := (Subgroup.center ↥K).pow_mem hwc _
  have hum : u ^ m = 1 := by
    rw [hu, ← pow_mul, ← hwm, pow_orderOf_eq_one]
  have hdvd : orderOf u ∣ m := orderOf_dvd_of_pow_eq_one hum
  have hcop : Nat.Coprime 3 (Nat.card (Subgroup.zpowers u)) := by
    rw [Nat.card_zpowers]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h => hm (h.trans hdvd)
  have hN : (Subgroup.zpowers u).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g u := Subgroup.mem_center_iff.1 huc g
    have hconj : g * u ^ k * g⁻¹ = u ^ k := by
      rw [(hc.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hconj]
    exact hn
  have hNle : Subgroup.zpowers u ≤ CFSG.pPrimeCore 3 ↥K := le_sSup ⟨hN, hcop⟩
  rw [hcore] at hNle
  have hu1 : u = 1 := Subgroup.mem_bot.1 (hNle (Subgroup.mem_zpowers u))
  refine ⟨a, Subtype.ext ?_⟩
  simpa [hu] using hu1

theorem center_bot_of_KHyp_td42
    {K B : Subgroup Y} (hK : KHyp 3 K B)
    (hc : catalogIs (↥K ⧸ Subgroup.center ↥K) fTD42) :
    Subgroup.center ↥K = ⊥ := by
  have hL := CFSG.LocalAnalysis.GLTheoremA.CatB.blueprintLieModel_td4two hc
  exact CFSG.RankThree.PartTwo.Sec4.Res6Seitz.center_eq_bot_of_trialityD4
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K).2.2.1.mpr hK.qs)
    (isPGroup_center_of_core hK.core) (hL.chevalleyExceptionalModel (by decide))

end Center

@[expose] def TD42OuterFix : Prop :=
  ∀ (S : Type) [Group S] [Finite S], catalogIs S fTD42 → ∀ D : Subgroup (MulAut S),
    IsElemAbelian 3 D → Nat.card D = 9 → ¬ D ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner S →
      ∃ α ∈ D, α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner S ∧
        ∃ F : Subgroup S, IsElemAbelian 3 F ∧ Nat.card F = 9 ∧ ∀ x ∈ F, α x = x

section Aux2

variable {G : Type*} [Group G]

theorem comm_mem_of_isMulCommutative (H : Subgroup G) [IsMulCommutative H] {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) : a * b = b * a := by
  have h := (IsMulCommutative.is_comm (M := H)).comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg Subtype.val h

theorem isMulCommutative_of_forall (H : Subgroup G) (h : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    IsMulCommutative H :=
  ⟨⟨fun a b => Subtype.ext (h a.1 a.2 b.1 b.2)⟩⟩

theorem comm_sup_forall {H L : Subgroup G} (hH : ∀ h1 ∈ H, ∀ h2 ∈ H, h1 * h2 = h2 * h1)
    (hL : ∀ l1 ∈ L, ∀ l2 ∈ L, l1 * l2 = l2 * l1) (hc : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h) :
    ∀ x ∈ H ⊔ L, ∀ y ∈ H ⊔ L, x * y = y * x := by
  intro a ha b hb
  obtain ⟨h1, hh1, l1, hl1, e1⟩ := mem_sup_exists_of_commute hc ha
  obtain ⟨h2, hh2, l2, hl2, e2⟩ := mem_sup_exists_of_commute hc hb
  rw [← e1, ← e2]
  calc h1 * l1 * (h2 * l2) = h1 * (l1 * h2) * l2 := by group
    _ = h1 * (h2 * l1) * l2 := by rw [hc h2 hh2 l1 hl1]
    _ = (h1 * h2) * (l1 * l2) := by group
    _ = (h2 * h1) * (l2 * l1) := by rw [hH h1 hh1 h2 hh2, hL l1 hl1 l2 hl2]
    _ = h2 * (h1 * l2) * l1 := by group
    _ = h2 * (l2 * h1) * l1 := by rw [hc h1 hh1 l2 hl2]
    _ = h2 * l2 * (h1 * l1) := by group

theorem pow3_sup_forall {H L : Subgroup G} (hH : ∀ h ∈ H, h ^ 3 = 1) (hL : ∀ l ∈ L, l ^ 3 = 1)
    (hc : ∀ h ∈ H, ∀ l ∈ L, h * l = l * h) :
    ∀ x ∈ H ⊔ L, x ^ 3 = 1 := by
  intro x hx
  obtain ⟨h1, hh1, l1, hl1, rfl⟩ := mem_sup_exists_of_commute hc hx
  have hcom : Commute h1 l1 := hc h1 hh1 l1 hl1
  rw [hcom.mul_pow, hH h1 hh1, hL l1 hl1, one_mul]

theorem mem_normalizer_of_comm {H : Subgroup G} {g : G} (hg : ∀ h ∈ H, g * h = h * g) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  constructor
  · intro hn
    have h1 : g * n * g⁻¹ = n := by rw [hg n hn]; group
    rw [h1]
    exact hn
  · intro hn
    have h1 := hg _ hn
    have key : g⁻¹ * (g * n * g⁻¹) * g = g * n * g⁻¹ := by
      calc g⁻¹ * (g * n * g⁻¹) * g = g⁻¹ * ((g * n * g⁻¹) * g) := by group
        _ = g⁻¹ * (g * (g * n * g⁻¹)) := by rw [h1]
        _ = g * n * g⁻¹ := by group
    have hnh : n = g * n * g⁻¹ := by
      calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
        _ = g * n * g⁻¹ := key
    exact (congrArg (fun x => x ∈ H) hnh).mpr hn

theorem isElemAbelian_map_of_forall {G' : Type*} [Group G'] (f : G →* G') (hf : Function.Injective f)
    {H : Subgroup G} (hcomm : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hexp : ∀ x ∈ H, x ^ 3 = 1) :
    IsElemAbelian 3 (H.map f) := by
  refine ⟨isMulCommutative_of_forall _ ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hexp x hx, map_one]

end Aux2

end CFSG.LocalAnalysis.GLTheoremA
