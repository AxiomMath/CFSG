module

import CFSG.Goldschmidt.Steps.Sec8Basic
import CFSG.Goldschmidt.Steps.Sec8Tools
import CFSG.Goldschmidt.Steps.Sec84b
import CFSG.Goldschmidt.Steps.Sec85a
import CFSG.Goldschmidt.Steps.G76U34
import CFSG.Goldschmidt.Steps.G76TypeI
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Goldschmidt.BasicG

public section

namespace CFSG.Goldschmidt.Sec8

open CFSG.Open

section Frattini

variable {X : Type} [Group X] [Finite X]

theorem exists_mem_normalizer_of_maximal {N R : Subgroup X} (hRN : R ≤ N) (hR2 : IsPGroup 2 R)
    (hmax : ∀ Y : Subgroup X, Y ≤ N → IsPGroup 2 Y → Nat.card Y ≤ Nat.card R) {m : X}
    (hm : m ∈ Subgroup.normalizer (N : Set X)) :
    ∃ n ∈ N, n⁻¹ * m ∈ Subgroup.normalizer (R : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : ∀ Y : Subgroup X, Y ≤ N → IsPGroup 2 Y → Nat.card R ≤ Nat.card Y →
      ∃ P : Sylow 2 N, (P : Subgroup N) = Y.subgroupOf N := by
    intro Y hYN hY2 hYc
    obtain ⟨P, hP⟩ := (hY2.comap_subtype (K := N)).exists_le_sylow
    refine ⟨P, (Subgroup.eq_of_le_of_card_ge hP ?_).symm⟩
    have h1 := hmax ((P : Subgroup N).map N.subtype) (Subgroup.map_subtype_le _)
      (P.isPGroup'.map _)
    rw [Subgroup.card_map_of_injective N.subtype_injective] at h1
    change Nat.card P ≤ Nat.card (Y.subgroupOf N)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYN).toEquiv]
    omega
  set R₂ := R.map (MulAut.conj m).toMonoidHom with hR₂
  have hR₂N : R₂ ≤ N := by
    rintro _ ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hm y).mp (hRN hy)
  have hcR₂ : Nat.card R₂ = Nat.card R :=
    Subgroup.card_map_of_injective (MulAut.conj m).injective
  obtain ⟨P₁, hP₁⟩ := hsyl R hRN hR2 le_rfl
  obtain ⟨P₂, hP₂⟩ := hsyl R₂ hR₂N (hR2.map _) hcR₂.ge
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq N P₁ P₂
  refine ⟨c, c.2, mem_normalizer_of_conj_le fun y hy => ?_⟩
  have h1 : (⟨y, hRN hy⟩ : N) ∈ (P₁ : Subgroup N) := hP₁ ▸ Subgroup.mem_subgroupOf.mpr hy
  have h2 : c * ⟨y, hRN hy⟩ * c⁻¹ ∈ (P₂ : Subgroup N) := by
    rw [← hc, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ h1
  rw [hP₂, Subgroup.mem_subgroupOf] at h2
  obtain ⟨z, hz, hzy⟩ := h2
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at hzy
  have e : ((c : X)⁻¹ * m)⁻¹ * y * ((c : X)⁻¹ * m) = z := by
    rw [show z = m⁻¹ * (m * z * m⁻¹) * m by group, hzy]
    group
  rw [e]
  exact hz

end Frattini

section Lift

theorem injOn_of_isPGroup {Y Q : Type} [Group Y] [Finite Y] [Group Q] (π : Y →* Q)
    (hπ : Odd (Nat.card π.ker)) {P : Subgroup Y} (hP : IsPGroup 2 P) :
    ∀ s ∈ P, ∀ t ∈ P, π s = π t → s = t := by
  intro s hs t ht hst
  have h1 : s⁻¹ * t ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hst, inv_mul_cancel]
  obtain ⟨k, hk⟩ := hP ⟨_, P.mul_mem (P.inv_mem hs) ht⟩
  have h2 := eq_one_of_pow_two_of_odd hπ h1 (k := k) (by simpa using congrArg Subtype.val hk)
  exact inv_mul_eq_one.mp h2

variable {G : Type} [Group G] [Finite G]

theorem exists_u34_data
    {S : Sylow 2 G} {A : Subgroup G} (hset : GoldSetting G S A)
    (h4 : Nat.card A = 4) {M : Subgroup G} (hAM : A ≤ M) {Q : Type} [Group Q] [Finite Q]
    (π : M →* Q) (hπs : Function.Surjective π) (hπ : Odd (Nat.card π.ker)) {L : Subgroup Q}
    (hLq : CFSG.Open.IsQuasisimple L) (e : L ⧸ Subgroup.center L ≃* PSU3 2 2)
    (hZ2 : ∀ z ∈ Subgroup.center L, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (hAL : (A.subgroupOf M).map π ≤ L)
    (hCN : Subgroup.centralizer (((A.subgroupOf M).map π : Subgroup Q) : Set Q) ≤
      Subgroup.normalizer (L : Set Q)) :
    ∃ R : Subgroup G, ∃ r : G, IsPGroup 2 R ∧ A ≤ R ∧ Nat.card R = 64 ∧ A ≤ ⁅R, R⁆ ∧
      r ∈ Subgroup.normalizer (R : Set G) ∧ r ∈ Subgroup.centralizer (A : Set G) ∧
      ∀ X : Subgroup G, X ≤ R → R ≤ Subgroup.normalizer (X : Set G) →
        r ∈ Subgroup.normalizer (X : Set G) → X ≤ A ∨ X = R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Ab := (A.subgroupOf M).map π with hAb
  have hA2 : IsPGroup 2 A := S.isPGroup'.to_le hset.le
  obtain ⟨TM, hATM⟩ := (hA2.comap_subtype (K := M)).exists_le_sylow
  have hinj := injOn_of_isPGroup π hπ TM.isPGroup'
  set T := (TM : Subgroup M).map π with hT
  have hTscoe : ((TM.mapSurjective hπs : Sylow 2 Q) : Subgroup Q) = T :=
    Sylow.coe_mapSurjective _ _
  have hT2 : IsPGroup 2 T := hTscoe ▸ (TM.mapSurjective hπs).isPGroup'
  have hTmax : ∀ P : Subgroup Q, IsPGroup 2 P → T ≤ P → P = T := fun P hP hTP => by
    rw [← hTscoe] at hTP ⊢
    exact (TM.mapSurjective hπs).is_maximal' hP hTP
  have hTMA : ∀ t ∈ (TM : Subgroup M), ∀ a ∈ A, a * (t : G) = t * a := by
    have hle := pGroup_le_centralizer hset h4 (R := (TM : Subgroup M).map M.subtype)
      (TM.isPGroup'.map _) (fun a ha => ⟨⟨a, hAM ha⟩, hATM ha, rfl⟩)
    exact fun t ht a ha => Subgroup.mem_centralizer_iff.mp (hle ⟨t, ht, rfl⟩) a ha
  have hTV : T ≤ Subgroup.centralizer (Ab : Set Q) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hTMA t ht a ha))
  have hVT : Ab ≤ T := Subgroup.map_mono hATM
  have hV4 : Nat.card Ab = 4 := by
    rw [hAb, G76.card_map_eq_of_injOn π (X := A.subgroupOf M) fun s hs t ht =>
        hinj s (hATM hs) t (hATM ht),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, h4]
  obtain ⟨-, -, -, h64, hcomm, r, -, hrN, hrC, hinvX⟩ :=
    G76.sylow_facts hLq e hZ2 hAL hV4 hT2 hTmax (hTV.trans hCN) hTV hVT
  set R' := (TM : Subgroup M) ⊓ L.comap π with hR'
  have hR'TM : R' ≤ TM := inf_le_left
  have hR'map : R'.map π = T ⊓ L := by
    apply le_antisymm
    · rintro _ ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs.1, rfl⟩, hs.2⟩
    · rintro q ⟨⟨s, hs, rfl⟩, hqL⟩
      exact ⟨s, ⟨hs, hqL⟩, rfl⟩
  set R := R'.map M.subtype with hR
  have hmemR : ∀ x : M, (x : G) ∈ R → x ∈ R' := fun x ⟨y, hy, hyx⟩ => by
    rwa [show x = y from Subtype.ext hyx.symm]
  have hinjR' : ∀ s ∈ R', ∀ t ∈ R', π s = π t → s = t := fun s hs t ht =>
    hinj s (hR'TM hs) t (hR'TM ht)
  have hAR' : ∀ a (ha : a ∈ A), (⟨a, hAM ha⟩ : M) ∈ R' := fun a ha =>
    ⟨hATM ha, hAL ⟨⟨a, hAM ha⟩, ha, rfl⟩⟩
  have hAR : A ≤ R := fun a ha => ⟨⟨a, hAM ha⟩, hAR' a ha, rfl⟩
  have hR2 : IsPGroup 2 R := (TM.isPGroup'.to_le hR'TM).map _
  have hcardR : Nat.card R = 64 := by
    rw [hR, Subgroup.card_map_of_injective M.subtype_injective, ← h64, ← hR'map,
      G76.card_map_eq_of_injOn π hinjR']
  have hARR : A ≤ ⁅R, R⁆ := by
    intro a ha
    have h1 : π ⟨a, hAM ha⟩ ∈ ⁅T ⊓ L, T ⊓ L⁆ := hcomm ⟨⟨a, hAM ha⟩, ha, rfl⟩
    rw [← hR'map, ← Subgroup.map_commutator] at h1
    obtain ⟨c, hc, hca⟩ := h1
    have hceq : c = ⟨a, hAM ha⟩ := hinjR' c (commutator_self_le R' hc) _ (hAR' a ha) hca
    rw [hR, ← Subgroup.map_commutator]
    exact ⟨c, hc, by rw [hceq]; rfl⟩
  obtain ⟨m, rfl⟩ := hπs r
  set N := (T ⊓ L).comap π with hN
  have hR'N : R' ≤ N := fun s hs => by
    rw [hN, Subgroup.mem_comap, ← hR'map]
    exact ⟨s, hs, rfl⟩
  have hmN : m ∈ Subgroup.normalizer (N : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [hN, Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hrN (π s)
  have hmax : ∀ Y : Subgroup M, Y ≤ N → IsPGroup 2 Y → Nat.card Y ≤ Nat.card R' := by
    intro Y hYN hY2
    rw [← G76.card_map_eq_of_injOn π (injOn_of_isPGroup π hπ hY2),
      ← G76.card_map_eq_of_injOn π hinjR', hR'map]
    exact Subgroup.card_le_of_le (Subgroup.map_le_iff_le_comap.mpr hYN)
  obtain ⟨n, hnN, hnm⟩ :=
    exists_mem_normalizer_of_maximal hR'N (TM.isPGroup'.to_le hR'TM) hmax hmN
  set rt : M := n⁻¹ * m with hrt
  have hπn : π n ∈ T ⊓ L := hnN
  have hπm : π m = π n * π rt := by rw [hrt, map_mul, map_inv, mul_inv_cancel_left]
  have hπr' : π rt ∈ Subgroup.centralizer (Ab : Set Q) := by
    rw [hrt, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTV hπn.1)) hrC
  refine ⟨R, (rt : G), hR2, hAR, hcardR, hARR, ?_, ?_, ?_⟩
  ·
    refine mem_normalizer_of_conj_le fun v hv => ?_
    obtain ⟨s, hs, rfl⟩ := hv
    refine ⟨_, (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnm) s).mp hs, ?_⟩
    simp
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := (Subgroup.mem_normalizer_iff.mp hnm _).mp (hAR' a ha)
    have h2 : π (rt * ⟨a, hAM ha⟩ * rt⁻¹) = π ⟨a, hAM ha⟩ := by
      rw [map_mul, map_mul, map_inv,
        ← Subgroup.mem_centralizer_iff.mp hπr' _ ⟨⟨a, hAM ha⟩, ha, rfl⟩]
      group
    have h3 := congrArg Subtype.val (hinjR' _ h1 _ (hAR' a ha) h2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    calc a * (rt : G) = (rt : G) * a * (rt : G)⁻¹ * rt := by rw [h3]
      _ = rt * a := by group
  ·
    intro X hXR hRX hrX
    set Xb := (X.subgroupOf M).map π with hXb
    have hXbTL : Xb ≤ T ⊓ L := by
      rintro _ ⟨x, hx, rfl⟩
      rw [← hR'map]
      exact ⟨x, hmemR x (hXR hx), rfl⟩
    have hnormXb : ∀ g : M, (g : G) ∈ Subgroup.normalizer (X : Set G) →
        π g ∈ Subgroup.normalizer (Xb : Set Q) := fun g hg =>
      Subgroup.le_normalizer_map π ⟨g, G76.mem_normalizer_subgroupOf hg, rfl⟩
    have hTLXb : T ⊓ L ≤ Subgroup.normalizer (Xb : Set Q) := by
      rw [← hR'map]
      rintro _ ⟨s, hs, rfl⟩
      exact hnormXb s (hRX ⟨s, hs, rfl⟩)
    have hrXb : π m ∈ Subgroup.normalizer (Xb : Set Q) := by
      rw [hπm]
      exact Subgroup.mul_mem _ (hTLXb hπn) (hnormXb _ hrX)
    rcases hinvX Xb hXbTL hTLXb hrXb with h | h
    · left
      intro x hx
      obtain ⟨s, hs, rfl⟩ := hXR hx
      obtain ⟨a', ha', ha's⟩ := h ⟨s, hx, rfl⟩
      rw [← hinj a' (hATM ha') s (hR'TM hs) ha's]
      exact ha'
    · right
      refine le_antisymm hXR fun y hy => ?_
      obtain ⟨s, hs, rfl⟩ := hy
      have h1 : π s ∈ Xb := by
        rw [h, ← hR'map]
        exact ⟨s, hs, rfl⟩
      obtain ⟨x, hx, hxs⟩ := h1
      rw [← hinjR' x (hmemR x (hXR hx)) s hs hxs]
      exact hx

end Lift

end CFSG.Goldschmidt.Sec8
