module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eSL2
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P85eLift

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
open scoped commutatorElement

structure LPairCtx (G : Type) [Group G] [Finite G] (z : G) (S : Subgroup G) : Prop where
  pair : ∃ L₁ L₂ : Subgroup (CentralizerBar z), SL2Pair (CentralizerBar z) L₁ L₂ ∧
    LBar z = L₁ ⊔ L₂ ∧ toBar z ⟨z, mem_Cen_self z⟩ ∈ L₁ ⊓ L₂ ∧
    ∀ g : CentralizerBar z, Odd (orderOf g) →
      g ∈ normalizer (L₁ : Set (CentralizerBar z)) ∧ g ∈ normalizer (L₂ : Set (CentralizerBar z))
  index : (RC S z).relIndex S ≤ 4

theorem SL2Pair.central_mem {Y : Type} [Group Y] {L₁ L₂ : Subgroup Y} (h : SL2Pair Y L₁ L₂) {x : Y}
    (hx : x ∈ L₁ ⊔ L₂) (hc : ∀ y ∈ L₁ ⊔ L₂, y * x = x * y) (hx2 : orderOf x = 2) :
    x ∈ L₁ ⊓ L₂ := by
  obtain ⟨t, ht₁, ht₂, ht2, hu₁, hu₂, -⟩ := h.exists_t
  obtain ⟨r₁, hr₁, h₁⟩ := h.sl₁
  obtain ⟨t₁, -, ht₁o, -, hc₁⟩ := CFSG.GH74.Generic.S1.sl2_involution_facts hr₁ h₁
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup' h.comm hx
  have haZ : ∀ w ∈ L₁, w * a = a * w := by
    intro w hw
    have h1 := hc w (Subgroup.mem_sup_left hw)
    have h2 := h.comm w hw b hb
    calc w * a = (w * (a * b)) * b⁻¹ := by group
      _ = ((a * b) * w) * b⁻¹ := by rw [h1]
      _ = a * (b * w) * b⁻¹ := by group
      _ = a * (w * b) * b⁻¹ := by rw [h2]
      _ = a * w := by group
  have haL₂ : a ∈ L₂ := by
    rcases hc₁ a ha (fun w hw => (haZ w hw).symm) with h1 | h1
    · rw [h1]; exact L₂.one_mem
    · have hsq : a * a = 1 := by
        rw [h1, ← sq]
        have := pow_orderOf_eq_one t₁
        rwa [ht₁o] at this
      rcases hu₁ a ha hsq with h3 | h3
      · rw [h3]; exact L₂.one_mem
      · rw [h3]; exact ht₂
  have hxL₂ : a * b ∈ L₂ := L₂.mul_mem haL₂ hb
  have hsq : (a * b) * (a * b) = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one (a * b)
    rwa [hx2] at this
  have hne : a * b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx2
    omega
  rcases hu₂ (a * b) hxL₂ hsq with h1 | h1
  · exact absurd h1 hne
  · rw [h1]; exact ⟨ht₁, ht₂⟩


section Bar

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem mem_barOf_iff {P : Subgroup G} {x : CentralizerBar z} :
    x ∈ barOf z P ↔ ∃ (y : G) (hy : y ∈ Cen z), y ∈ P ∧ toBar z ⟨y, hy⟩ = x := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(a : G), a.2, Subgroup.mem_subgroupOf.mp ha, rfl⟩
  · rintro ⟨y, hy, hyP, rfl⟩
    exact ⟨⟨y, hy⟩, Subgroup.mem_subgroupOf.mpr hyP, rfl⟩

theorem toBar_inj_of_pgroup {P : Subgroup G} (hP2 : IsPGroup 2 P) {x y : G} (hxP : x ∈ P) (hyP : y ∈ P)
    (hx : x ∈ Cen z) (hy : y ∈ Cen z) (h : toBar z ⟨x, hx⟩ = toBar z ⟨y, hy⟩) : x = y := by
  have hP' : IsPGroup 2 ↥(P.subgroupOf (Cen z)) := hP2.comap_subtype
  have hker : (⟨x, hx⟩ : ↥(Cen z))⁻¹ * ⟨y, hy⟩ ∈ (toBar z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have h2 : (⟨x, hx⟩ : ↥(Cen z))⁻¹ * ⟨y, hy⟩ ∈ P.subgroupOf (Cen z) :=
    (P.subgroupOf (Cen z)).mul_mem ((P.subgroupOf (Cen z)).inv_mem (Subgroup.mem_subgroupOf.mpr hxP))
      (Subgroup.mem_subgroupOf.mpr hyP)
  have := eq_one_of_pgroup_of_odd hP' (odd_card_ker_toBar z) h2 hker
  have h3 := congrArg Subtype.val this
  simpa [inv_mul_eq_one, eq_comm] using h3

theorem orderOf_zBar (hz2 : orderOf z = 2) : orderOf (toBar z ⟨z, mem_Cen_self z⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz1 : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ^ 2 = 1 := by
    apply Subtype.ext
    simpa using (hz2 ▸ pow_orderOf_eq_one z)
  have hzo : orderOf (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hz2
  apply orderOf_eq_prime
  · rw [← map_pow, hz1, map_one]
  · intro h
    have hk : (⟨z, mem_Cen_self z⟩ : ↥(Cen z)) ∈ (toBar z).ker := h
    have h1 : orderOf (⟨⟨z, mem_Cen_self z⟩, hk⟩ : (toBar z).ker) ∣ Nat.card (toBar z).ker :=
      orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hzo] at h1
    exact (Nat.not_even_iff_odd.mpr (odd_card_ker_toBar z)) (even_iff_two_dvd.mpr h1)

theorem LBar_normal (z : G) : (LBar z).Normal := Stage1.Thm6.Prod.LBar_isNormal z

theorem exists_psi {P : Subgroup G} (hP2 : IsPGroup 2 P) (hPC : P ≤ Cen z) :
    ∃ ψ : ↥P →* CentralizerBar z, Function.Injective ψ ∧
      (∀ x : ↥P, ψ x = toBar z ⟨(x : G), hPC x.2⟩) ∧ ψ.range = barOf z P := by
  refine ⟨(toBar z).comp (Subgroup.inclusion hPC), ?_, fun x => rfl, ?_⟩
  · intro x y hxy
    exact Subtype.ext (toBar_inj_of_pgroup hP2 x.2 y.2 (hPC x.2) (hPC y.2) hxy)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact mem_barOf_iff.mpr ⟨(x : G), hPC x.2, x.2, rfl⟩
    · intro hy
      obtain ⟨u, hu, huP, rfl⟩ := mem_barOf_iff.mp hy
      exact ⟨⟨u, huP⟩, rfl⟩

theorem lpair_card_le {S : Subgroup G} (hLP : LPairCtx G z S) (hSC : S ≤ Cen z)
    {P : Subgroup G} (hPS : P ≤ S) (hP2 : IsPGroup 2 P) :
    Nat.card P ≤ 4 * Nat.card ↥(barOf z P ⊓ LBar z) := by
  classical
  have hPC : P ≤ Cen z := hPS.trans hSC
  obtain ⟨ψ, hinj, hψ, hrange⟩ := exists_psi hP2 hPC
  set T : Subgroup G := P ⊓ LC z with hT
  have hTP : T ≤ P := inf_le_left
  have hidx : T.relIndex P ≤ 4 := by
    have h1 : (RC S z).relIndex S ≠ 0 := by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite
    have h2 := Subgroup.relIndex_le_of_le_right hPS h1
    have h3 : (RC S z ⊓ P) = T := by
      ext x
      simp only [RC, Subgroup.mem_inf, hT]
      constructor
      · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h', h⟩
      · rintro ⟨h', h⟩; exact ⟨⟨hPS h', h⟩, h'⟩
    rw [← h3, Subgroup.inf_relIndex_right]
    exact h2.trans hLP.index
  have hcard : Nat.card P = T.relIndex P * Nat.card T := by
    have := Subgroup.relIndex_mul_card (H := T) (K := P)
    rw [inf_eq_left.mpr hTP] at this
    exact this.symm
  have hTB : Nat.card T ≤ Nat.card ↥(barOf z P ⊓ LBar z) := by
    have hc1 : Nat.card ((T.subgroupOf P).map ψ) = Nat.card T := by
      rw [Subgroup.card_map_of_injective hinj]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTP).toEquiv
    rw [← hc1]
    apply Subgroup.card_le_of_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hxT : (x : G) ∈ T := hx
    refine ⟨?_, ?_⟩
    · rw [← hrange]; exact ⟨x, rfl⟩
    · rw [hψ]; exact mem_barOf_iff.mpr ⟨(x : G), hPC x.2, hxT.2, rfl⟩
  calc Nat.card P = T.relIndex P * Nat.card T := hcard
    _ ≤ 4 * Nat.card T := Nat.mul_le_mul_right _ hidx
    _ ≤ 4 * Nat.card ↥(barOf z P ⊓ LBar z) := Nat.mul_le_mul_left _ hTB

theorem lpair_z_mem (hz2 : orderOf z = 2) {S : Subgroup G} (hLP : LPairCtx G z S) (hSC : S ≤ Cen z)
    {P : Subgroup G} (hPS : P ≤ S) (hP2 : IsPGroup 2 P)
    (hord : ∀ x ∈ P, 8 * orderOf x < Nat.card P) : z ∈ P := by
  classical
  by_contra hzP
  obtain ⟨L₁, L₂, hpair, hL, hzL, -⟩ := hLP.pair
  have hPC : P ≤ Cen z := hPS.trans hSC
  obtain ⟨ψ, hinj, hψ, hrange⟩ := exists_psi hP2 hPC
  have hzb : toBar z ⟨z, mem_Cen_self z⟩ ∉ barOf z P := by
    intro hmem
    obtain ⟨y, hy, hyP, hyz⟩ := mem_barOf_iff.mp hmem
    exact hzP (z_mem_of_toBar_eq hz2 hyP hy hyz)
  have hPb2 : IsPGroup 2 ↥(barOf z P) := by
    rw [← hrange]
    exact (hP2.of_equiv (MonoidHom.ofInjective hinj))
  have hB2 : IsPGroup 2 ↥(barOf z P ⊓ LBar z) := hPb2.to_le inf_le_left
  have hBL : barOf z P ⊓ LBar z ≤ L₁ ⊔ L₂ := hL ▸ inf_le_right
  have htB : toBar z ⟨z, mem_Cen_self z⟩ ∉ barOf z P ⊓ LBar z := fun h => hzb h.1
  obtain ⟨xb, hxB, hx⟩ := pair_cyc_index hpair hzL (orderOf_zBar hz2) hBL hB2 htB
  obtain ⟨u, hu, huP, hux⟩ := mem_barOf_iff.mp hxB.1
  have hord_u : orderOf (toBar z ⟨u, hu⟩) = orderOf u := by
    have h1 : ψ ⟨u, huP⟩ = toBar z ⟨u, hu⟩ := by rw [hψ]
    rw [← h1, orderOf_injective ψ hinj]
    exact (Subgroup.orderOf_coe ⟨u, huP⟩).symm
  have hcard := lpair_card_le hLP hSC hPS hP2
  have := hord u huP
  rw [hux] at hord_u
  omega

omit [Finite G] in
theorem conj_mem_barOf {P : Subgroup G} {g : G} (hg : g ∈ Cen z) (hgP : g ∈ normalizer (P : Set G))
    {h : CentralizerBar z} (hh : h ∈ barOf z P) :
    toBar z ⟨g, hg⟩ * h * (toBar z ⟨g, hg⟩)⁻¹ ∈ barOf z P := by
  obtain ⟨y, hy, hyP, rfl⟩ := mem_barOf_iff.mp hh
  refine mem_barOf_iff.mpr ⟨g * y * g⁻¹, ?_, ?_, ?_⟩
  · exact (Cen z).mul_mem ((Cen z).mul_mem hg hy) ((Cen z).inv_mem hg)
  · exact (mem_normalizer_iff.mp hgP y).mp hyP
  · rw [← map_inv, ← map_mul, ← map_mul]
    rfl

theorem lpair_comm_trivial {S : Subgroup G} (hLP : LPairCtx G z S) (hSC : S ≤ Cen z)
    {P : Subgroup G} (hPS : P ≤ S) (hP2 : IsPGroup 2 P) {w : G} (hwC : w ∈ Cen z)
    (hwP : w ∈ normalizer (P : Set G)) {a : ℕ} (hw5 : w ^ (5 ^ a) = 1) : ⁅P, zpowers w⁆ = ⊥ := by
  classical
  obtain ⟨L₁, L₂, hpair, hL, hzL, hodd⟩ := hLP.pair
  have hPC : P ≤ Cen z := hPS.trans hSC
  obtain ⟨ψ, hinj, hψ, hrange⟩ := exists_psi hP2 hPC
  have hPb2 : IsPGroup 2 ↥(barOf z P) := by
    rw [← hrange]
    exact (hP2.of_equiv (MonoidHom.ofInjective hinj))
  set wb : CentralizerBar z := toBar z ⟨w, hwC⟩ with hwb
  have hwb5 : wb ^ (5 ^ a) = 1 := by
    rw [hwb, ← map_pow]
    have : (⟨w, hwC⟩ : ↥(Cen z)) ^ (5 ^ a) = 1 := Subtype.ext (by simpa using hw5)
    rw [this, map_one]
  set W : Subgroup (CentralizerBar z) := Subgroup.zpowers wb with hW
  have hW5 : IsPGroup 5 ↥W := by
    intro g
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨a, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hwb5, one_zpow]
  have hWodd : ∀ g ∈ W, Odd (orderOf g) := by
    intro g hg
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    have : g ^ (5 ^ a) = 1 := by
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hwb5, one_zpow]
    have hd : orderOf g ∣ 5 ^ a := orderOf_dvd_of_pow_eq_one this
    exact Odd.of_dvd_nat (Odd.pow (by decide)) hd
  have hWP : W ≤ normalizer (↑(barOf z P) : Set (CentralizerBar z)) := by
    rw [hW, Subgroup.zpowers_le]
    rw [mem_normalizer_iff]
    have hwinv : w⁻¹ ∈ normalizer (P : Set G) := Subgroup.inv_mem _ hwP
    have hwinvC : w⁻¹ ∈ Cen z := (Cen z).inv_mem hwC
    intro h
    constructor
    · intro hh
      exact conj_mem_barOf hwC hwP hh
    · intro hh
      have h2 := conj_mem_barOf hwinvC hwinv hh
      have h3 : toBar z ⟨w⁻¹, hwinvC⟩ = wb⁻¹ := by rw [hwb, ← map_inv]; rfl
      rw [h3, inv_inv] at h2
      have h4 : wb⁻¹ * (wb * h * wb⁻¹) * wb = h := by group
      rwa [h4] at h2
  have hW₁ : W ≤ normalizer (L₁ : Set (CentralizerBar z)) := fun g hg => (hodd g (hWodd g hg)).1
  have hW₂ : W ≤ normalizer (L₂ : Set (CentralizerBar z)) := fun g hg => (hodd g (hWodd g hg)).2
  have hLn : (L₁ ⊔ L₂).Normal := hL ▸ LBar_normal z
  have hidx : (barOf z P ⊓ (L₁ ⊔ L₂)).relIndex (barOf z P) ≤ 4 := by
    have h1 := Subgroup.relIndex_mul_card (H := barOf z P ⊓ (L₁ ⊔ L₂)) (K := barOf z P)
    have h2 := lpair_card_le hLP hSC hPS hP2
    have h3 : Nat.card (barOf z P) = Nat.card P := by
      rw [← hrange]
      exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have h4 : barOf z P ⊓ (L₁ ⊔ L₂) ⊓ barOf z P = barOf z P ⊓ LBar z := by
      rw [← hL]; ext x; simp only [Subgroup.mem_inf]; tauto
    rw [h4] at h1
    have hpos : 0 < Nat.card ↥(barOf z P ⊓ LBar z) := Nat.card_pos
    rw [h3] at h1
    by_contra hcon
    push Not at hcon
    have := Nat.mul_lt_mul_of_pos_right hcon hpos
    omega
  have hkl := pair_kl hpair hLn hPb2 hidx hW5 hWP hW₁ hW₂
  have hcomm : ∀ x ∈ P, x * w = w * x := by
    intro x hx
    have hxC : x ∈ Cen z := hPC hx
    have hc : (⁅x, w⁆ : G) ∈ P := by
      have h1 : w * x⁻¹ * w⁻¹ ∈ P := (mem_normalizer_iff.mp hwP x⁻¹).mp (P.inv_mem hx)
      rw [commutatorElement_def]
      have : x * w * x⁻¹ * w⁻¹ = x * (w * x⁻¹ * w⁻¹) := by group
      rw [this]
      exact P.mul_mem hx h1
    have hcC : (⁅x, w⁆ : G) ∈ Cen z := by
      have := (Cen z).mul_mem ((Cen z).mul_mem ((Cen z).mul_mem hxC hwC) ((Cen z).inv_mem hxC))
        ((Cen z).inv_mem hwC)
      simpa [commutatorElement_def] using this
    have hmem : toBar z ⟨⁅x, w⁆, hcC⟩ ∈ ⁅barOf z P, W⁆ := by
      have : toBar z ⟨⁅x, w⁆, hcC⟩ = ⁅toBar z ⟨x, hxC⟩, wb⁆ := by
        rw [hwb, ← map_commutatorElement]; rfl
      rw [this]
      exact Subgroup.commutator_mem_commutator (mem_barOf_iff.mpr ⟨x, hxC, hx, rfl⟩)
        (Subgroup.mem_zpowers wb)
    rw [hkl, Subgroup.mem_bot] at hmem
    have h1 : toBar z ⟨⁅x, w⁆, hcC⟩ = toBar z ⟨1, (Cen z).one_mem⟩ := by
      rw [hmem]; exact (map_one (toBar z)).symm
    have := toBar_inj_of_pgroup hP2 hc P.one_mem hcC (Cen z).one_mem h1
    exact (commutatorElement_eq_one_iff_mul_comm).mp this
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (Commute.zpow_left (hcomm x hx).symm k).eq

end Bar

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.P85
