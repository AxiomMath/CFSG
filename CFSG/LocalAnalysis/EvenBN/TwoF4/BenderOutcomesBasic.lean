module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.CosetInvolutions
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section Ambient

variable {H : Type*} [Group H]

abbrev zIn (W : Subgroup H) : Subgroup H := centralizer (W : Set H) ⊓ W

theorem mem_zIn {W : Subgroup H} {z : H} :
    z ∈ zIn W ↔ (∀ w ∈ W, w * z = z * w) ∧ z ∈ W := by
  rw [mem_inf, mem_centralizer_iff]
  rfl

theorem zIn_le (W : Subgroup H) : zIn W ≤ W := inf_le_right

theorem le_normalizer_zIn (W : Subgroup H) : W ≤ normalizer (zIn W : Set H) := by
  intro w hw
  rw [mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have hzw := (mem_zIn.mp hz).1 w hw
    have : w * z * w⁻¹ = z := by rw [hzw]; group
    rw [this]
    exact hz
  · intro hz
    have hzw := (mem_zIn.mp hz).1 w hw
    have : w * z * w⁻¹ = z := by
      have h2 : w * (w * z * w⁻¹) = w * z := by
        calc w * (w * z * w⁻¹) = w * z * w⁻¹ * w := hzw
          _ = w * z := by group
      exact mul_left_cancel h2
    rw [this] at hz
    exact hz

theorem mem_normalizer_zIn {W : Subgroup H} {g : H} (hg : g ∈ normalizer (W : Set H)) :
    g ∈ normalizer (zIn W : Set H) := by
  have hg' := mem_normalizer_iff''.mp hg
  rw [mem_normalizer_iff] at hg ⊢
  intro z
  simp only [mem_zIn]
  constructor
  · rintro ⟨hz, hzW⟩
    refine ⟨fun w hw => ?_, (hg z).mp hzW⟩
    have hw' : g⁻¹ * w * g ∈ W := (hg' w).mp hw
    have h1 := hz _ hw'
    calc w * (g * z * g⁻¹) = g * (g⁻¹ * w * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * w * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * w := by group
  · rintro ⟨hz, hzW⟩
    refine ⟨fun w hw => ?_, (hg z).mpr hzW⟩
    have hw' : g * w * g⁻¹ ∈ W := (hg w).mp hw
    have h1 := hz _ hw'
    have h2 : g * (w * z) * g⁻¹ = g * (z * w) * g⁻¹ := by
      calc g * (w * z) * g⁻¹ = g * w * g⁻¹ * (g * z * g⁻¹) := by group
        _ = g * z * g⁻¹ * (g * w * g⁻¹) := h1
        _ = g * (z * w) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem exists_eq_or_eq_mul_of_mem_sup {W : Subgroup H} {a : H} (haa : a * a = 1)
    (ha : a ∈ normalizer (W : Set H)) {x : H} (hx : x ∈ W ⊔ zpowers a) :
    ∃ w ∈ W, x = w ∨ x = w * a := by
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left W (zpowers a)
    (zpowers_le.mpr ha), Set.mem_mul] at hx
  obtain ⟨w, hw, b, hb, rfl⟩ := hx
  rcases eq_one_or_eq_of_mem_zpowers haa hb with rfl | rfl
  · exact ⟨w, hw, Or.inl (mul_one w)⟩
  · exact ⟨w, hw, Or.inr rfl⟩

theorem exists_mul_of_mem_sup_zIn {V W : Subgroup H} (hVW : V ≤ W) {x : H}
    (hx : x ∈ V ⊔ zIn W) : ∃ v ∈ V, ∃ z ∈ zIn W, x = v * z := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right V (zIn W)
    (hVW.trans (le_normalizer_zIn W)), Set.mem_mul] at hx
  obtain ⟨v, hv, z, hz, rfl⟩ := hx
  exact ⟨v, hv, z, hz, rfl⟩

structure BenderSylow (D : Subgroup H) (a : H) (V W : Subgroup H) : Prop where
  mul_self : a * a = 1
  not_mem : a ∉ D
  le_D : W ≤ D
  isPGroup : IsPGroup 2 W
  le : V ≤ W
  unique : ∀ S : Subgroup H, S ≤ D → IsPGroup 2 S → V ≤ S → S ≤ W
  conj_mem : ∀ w ∈ W, a⁻¹ * w * a ∈ W
  inf_centralizer : W ⊓ centralizer ({a} : Set H) = V
  center_mul_self : ∀ z ∈ zIn W, z * z = 1
  mul_self_mem : ∀ w ∈ W, w * w ∈ zIn W
  center_comm_mem : ∀ z ∈ zIn W, z⁻¹ * (a⁻¹ * z * a) ∈ zIn V
  exists_center_comm : ∀ v ∈ zIn V, ∃ z ∈ zIn W, v = z⁻¹ * (a⁻¹ * z * a)
  comm_mem : ∀ w ∈ W, w⁻¹ * (a⁻¹ * w * a) ∈ ⁅W, W⁆ ⊔ V
  le_commutator : ⁅W, W⁆ ⊔ V ≤ ⁅W, zpowers a⁆
  exists_comm_mod : ∀ v ∈ V, ∃ y ∈ W, v⁻¹ * (y⁻¹ * (a⁻¹ * y * a)) ∈ zIn W
  mem_of_comm : ∀ w ∈ W, w⁻¹ * (a⁻¹ * w * a) ∈ zIn W → w ∈ V ⊔ zIn W
  mem_center : ∀ v ∈ V, v * v = 1 → v ∈ zIn W

namespace BenderSylow

variable {D : Subgroup H} {a : H} {V W : Subgroup H} (h : BenderSylow D a V W)
include h

theorem inv_eq : a⁻¹ = a := inv_eq_of_mul_eq_one_right h.mul_self

theorem not_mem_W : a ∉ W := fun haW => h.not_mem (h.le_D haW)

theorem mem_normalizer : a ∈ normalizer (W : Set H) := by
  rw [mem_normalizer_iff'']
  intro w
  refine ⟨fun hw => h.conj_mem w hw, fun hw => ?_⟩
  have := h.conj_mem _ hw
  rwa [h.inv_eq, show a * (a * w * a) * a = (a * a) * w * (a * a) by group, h.mul_self,
    one_mul, mul_one] at this

theorem le_centralizer : V ≤ centralizer ({a} : Set H) := by
  rw [← h.inf_centralizer]
  exact inf_le_right

theorem zIn_V_le : zIn V ≤ zIn W := by
  intro v hv
  obtain ⟨z, hz, rfl⟩ := h.exists_center_comm v hv
  have hza : a⁻¹ * z * a ∈ zIn W := by
    have := mem_normalizer_zIn h.mem_normalizer
    have h1 := (mem_normalizer_iff''.mp this z).mp hz
    exact h1
  exact mul_mem (inv_mem hz) hza

theorem freeSeries : FreeSeries a ![⊥, zIn W, W] where
  bot := rfl
  le_succ := by
    intro i
    fin_cases i
    · exact bot_le
    · exact zIn_le W
  le_normalizer := by
    intro i
    fin_cases i
    · change zIn W ≤ normalizer ((⊥ : Subgroup H) : Set H)
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
    · exact le_normalizer_zIn W
  mem_normalizer := by
    intro i
    fin_cases i
    · change a ∈ normalizer ((⊥ : Subgroup H) : Set H)
      rw [normalizer_eq_top_iff.mpr inferInstance]
      exact mem_top a
    · exact mem_normalizer_zIn h.mem_normalizer
    · exact h.mem_normalizer
  mul_self_mem := by
    intro i
    fin_cases i
    · intro x hx
      change x * x ∈ (⊥ : Subgroup H)
      rw [h.center_mul_self x hx]
      exact one_mem _
    · exact h.mul_self_mem
  exists_commutator := by
    intro i
    fin_cases i
    · intro x hx hxa
      change x ∈ zIn W at hx
      change a⁻¹ * x⁻¹ * a * x ∈ (⊥ : Subgroup H) at hxa
      change ∃ y ∈ zIn W, x⁻¹ * (y⁻¹ * (a⁻¹ * y * a)) ∈ (⊥ : Subgroup H)
      rw [mem_bot] at hxa
      have hxc : x ∈ centralizer ({a} : Set H) := by
        rw [mem_centralizer_singleton_iff]
        calc x * a = x * (a * (a⁻¹ * x⁻¹ * a * x)) := by rw [hxa, mul_one]
          _ = a * x := by group
      have hxV : x ∈ V := by
        rw [← h.inf_centralizer]
        exact ⟨zIn_le W hx, hxc⟩
      have hxZV : x ∈ zIn V := by
        refine mem_zIn.mpr ⟨fun v hv => (mem_zIn.mp hx).1 v (h.le hv), hxV⟩
      obtain ⟨y, hy, hxy⟩ := h.exists_center_comm x hxZV
      refine ⟨y, hy, ?_⟩
      rw [← hxy, inv_mul_cancel]
      exact one_mem _
    · intro x hx hxa
      change x ∈ W at hx
      change a⁻¹ * x⁻¹ * a * x ∈ zIn W at hxa
      change ∃ y ∈ W, x⁻¹ * (y⁻¹ * (a⁻¹ * y * a)) ∈ zIn W
      have hxa' : x⁻¹ * (a⁻¹ * x * a) ∈ zIn W := by
        have := inv_mem hxa
        rwa [show (a⁻¹ * x⁻¹ * a * x)⁻¹ = x⁻¹ * (a⁻¹ * x * a) by group] at this
      obtain ⟨v, hv, z, hz, rfl⟩ := exists_mul_of_mem_sup_zIn h.le (h.mem_of_comm x hx hxa')
      obtain ⟨y, hy, hvy⟩ := h.exists_comm_mod v hv
      refine ⟨y, hy, ?_⟩
      rw [show (v * z)⁻¹ * (y⁻¹ * (a⁻¹ * y * a)) = z⁻¹ * (v⁻¹ * (y⁻¹ * (a⁻¹ * y * a))) by
        group]
      exact mul_mem (inv_mem hz) hvy

theorem mem_normalizer_V : a ∈ normalizer (V : Set H) := by
  rw [mem_normalizer_iff'']
  intro v
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · have hva := mem_centralizer_singleton_iff.mp (h.le_centralizer hv)
    rw [mul_assoc, hva, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hv
  · have hy := mem_centralizer_singleton_iff.mp (h.le_centralizer hv)
    have : v = a⁻¹ * v * a := by
      calc v = a * (a⁻¹ * v * a) * a⁻¹ := by group
        _ = (a⁻¹ * v * a) * a * a⁻¹ := by rw [← hy]
        _ = a⁻¹ * v * a := by group
    rw [this]
    exact hv

theorem mem_sup_zIn_of_conj_mem {w : H} (hw : w ∈ W) (hwa : w⁻¹ * a * w ∈ V ⊔ zpowers a) :
    w ∈ V ⊔ zIn W := by
  have haV : a ∈ normalizer (V : Set H) := h.mem_normalizer_V
  obtain ⟨v, hv, hcase | hcase⟩ := exists_eq_or_eq_mul_of_mem_sup h.mul_self haV hwa
  · exfalso
    apply h.not_mem_W
    have : a = w * v * w⁻¹ := by rw [← hcase]; group
    rw [this]
    exact mul_mem (mul_mem hw (h.le hv)) (inv_mem hw)
  · have hva : v * a = a * v := mem_centralizer_singleton_iff.mp (h.le_centralizer hv)
    have hv2 : v * v = 1 := by
      have h1 : w⁻¹ * (a * a) * w = (v * a) * (v * a) := by
        rw [← hcase]; group
      rw [h.mul_self, show w⁻¹ * 1 * w = 1 by group,
        show v * a * (v * a) = v * v * (a * a) by
          rw [mul_assoc v a (v * a), ← mul_assoc a v a, ← hva]; group, h.mul_self,
        mul_one] at h1
      exact h1.symm
    have hcomm : w⁻¹ * (a⁻¹ * w * a) = v := by
      rw [h.inv_eq]
      calc w⁻¹ * (a * w * a) = (w⁻¹ * a * w) * a := by group
        _ = v * a * a := by rw [hcase]
        _ = v := by rw [mul_assoc, h.mul_self, mul_one]
    exact h.mem_of_comm w hw (hcomm ▸ h.mem_center v hv hv2)

theorem le_sup_of_isPGroup [Finite H] [D.Normal]
    (hC : IsSylowOf 2 (V ⊔ zpowers a) (centralizer ({a} : Set H))) {S : Subgroup H}
    (hS : IsPGroup 2 S) (hVS : V ⊔ zpowers a ≤ S) : S ≤ W ⊔ zpowers a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hST⟩ := hS.exists_le_sylow
  suffices hT : (T : Subgroup H) = W ⊔ zpowers a from hT ▸ hST
  have hVT : V ⊔ zpowers a ≤ T := hVS.trans hST
  have hTsyl : IsSylowOf 2 (T : Subgroup H) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, T.isPGroup', ?_⟩
    rw [relIndex_top_right]
    exact T.not_dvd_index
  have hTD : IsSylowOf 2 ((T : Subgroup H) ⊓ D) D :=
    hTsyl.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr inferInstance])
  have hTDW : (T : Subgroup H) ⊓ D ≤ W :=
    h.unique _ inf_le_right (T.isPGroup'.to_le inf_le_left)
      (le_inf (le_sup_left.trans hVT) (h.le.trans h.le_D))
  have hWeq : W = (T : Subgroup H) ⊓ D := hTD.eq_of_le hTDW h.le_D h.isPGroup
  have hWT : W ≤ T := hWeq ▸ inf_le_left
  have haT : a ∈ T := hVT (mem_sup_right (mem_zpowers a))
  have hMT : W ⊔ zpowers a ≤ T := sup_le hWT (zpowers_le.mpr haT)
  have hTC : (T : Subgroup H) ⊓ centralizer {a} = V ⊔ zpowers a := by
    refine hC.eq_of_le (le_inf hVT ?_) inf_le_right (T.isPGroup'.to_le inf_le_left)
    exact sup_le h.le_centralizer (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl))
  refine le_antisymm ?_ hMT
  by_contra hne
  set M : Subgroup T := (W ⊔ zpowers a).subgroupOf T with hMdef
  have hMlt : M < ⊤ := by
    refine lt_of_le_of_ne le_top fun hMtop => hne fun x hx => ?_
    have : (⟨x, hx⟩ : T) ∈ M := hMtop ▸ mem_top _
    exact this
  have : Group.IsNilpotent (T : Subgroup H) := T.isPGroup'.isNilpotent
  obtain ⟨s, hsN, hsM⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent M hMlt)
  apply hsM
  have hsW : (s : H) ∈ normalizer (W : Set H) := by
    rw [mem_normalizer_iff]
    intro w
    rw [hWeq]
    constructor
    · intro hw'
      obtain ⟨hwT, hwD⟩ := mem_inf.mp hw'
      exact mem_inf.mpr ⟨mul_mem (mul_mem s.2 hwT) (inv_mem s.2),
        (inferInstance : D.Normal).conj_mem w hwD s⟩
    · intro hw'
      obtain ⟨hwT, hwD⟩ := mem_inf.mp hw'
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have := mul_mem (mul_mem (inv_mem s.2) hwT) s.2
        rwa [show (s : H)⁻¹ * (s * w * (s : H)⁻¹) * s = w by group] at this
      · have := (inferInstance : D.Normal).conj_mem _ hwD (s : H)⁻¹
        rwa [show (s : H)⁻¹ * (s * w * (s : H)⁻¹) * (s : H)⁻¹⁻¹ = w by group] at this
  have hsa : (s : H)⁻¹ * a * s ∈ W ⊔ zpowers a := by
    have h1 := (mem_normalizer_iff''.mp hsN ⟨a, haT⟩).mp (mem_sup_right (mem_zpowers a))
    exact h1
  obtain ⟨w, hw, hsw | hsw⟩ := exists_eq_or_eq_mul_of_mem_sup h.mul_self h.mem_normalizer hsa
  · exfalso
    apply h.not_mem_W
    have h2 := (mem_normalizer_iff.mp hsW w).mp hw
    rwa [← hsw, show (s : H) * ((s : H)⁻¹ * a * s) * (s : H)⁻¹ = a by group] at h2
  ·
    have hsc : (s : H) ∈ sectionCentralizer (zpowers a ⊔ W) W := by
      rw [mem_sectionCentralizer_zpowers_sup_iff h.mem_normalizer]
      refine ⟨hsW, ?_⟩
      rw [show a⁻¹ * (s : H)⁻¹ * a * s = a⁻¹ * ((s : H)⁻¹ * a * s) by group, hsw,
        show a⁻¹ * (w * a) = a⁻¹ * w * a by group]
      exact h.conj_mem w hw
    have hsec := h.freeSeries.sectionCentralizer_eq h.mul_self
    change sectionCentralizer (zpowers a ⊔ W) W =
      W ⊔ (normalizer (W : Set H) ⊓ centralizer ({a} : Set H)) at hsec
    rw [hsec] at hsc
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left W _ inf_le_left, Set.mem_mul]
      at hsc
    obtain ⟨w', hw', c, hc, hwc⟩ := hsc
    have hcT : c ∈ (T : Subgroup H) := by
      have : c = w'⁻¹ * s := by rw [← hwc]; group
      rw [this]
      exact mul_mem (inv_mem (hWT hw')) s.2
    have hcM : c ∈ V ⊔ zpowers a := hTC ▸ ⟨hcT, hc.2⟩
    change (s : H) ∈ W ⊔ zpowers a
    rw [← hwc]
    exact mul_mem (mem_sup_left hw') (sup_le (le_sup_left.trans (sup_le_sup_right h.le _))
      le_sup_right hcM)

theorem isPGroup_sup : IsPGroup 2 (W ⊔ zpowers a : Subgroup H) := by
  have hz : IsPGroup 2 (zpowers a) := by
    have h1 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, h.mul_self])
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h2 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h2, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])
  rw [sup_comm]
  exact hz.to_sup_of_normal_right' h.isPGroup (zpowers_le.mpr h.mem_normalizer)

end BenderSylow

theorem map_zIn {X : Type*} [Group X] {φ : X →* H} (hφ : Function.Injective φ)
    (W : Subgroup X) : (zIn W).map φ = zIn (W.map φ) := by
  ext z
  constructor
  · rintro ⟨z₀, hz₀, rfl⟩
    obtain ⟨hc, hzW⟩ := mem_zIn.mp hz₀
    refine mem_zIn.mpr ⟨?_, mem_map_of_mem φ hzW⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← map_mul, hc w hw]
  · intro hz
    obtain ⟨hc, hzW⟩ := mem_zIn.mp hz
    obtain ⟨z₀, hz₀, rfl⟩ := hzW
    refine ⟨z₀, mem_zIn.mpr ⟨fun w hw => hφ ?_, hz₀⟩, rfl⟩
    rw [map_mul, map_mul]
    exact hc _ (mem_map_of_mem φ hw)

structure BenderSylowAut {X : Type*} [Group X] (τ : MulAut X) (V W : Subgroup X) : Prop where
  isPGroup : IsPGroup 2 W
  le : V ≤ W
  unique : ∀ S : Subgroup X, IsPGroup 2 S → V ≤ S → S ≤ W
  mem : ∀ w ∈ W, τ w ∈ W
  fixed : ∀ w ∈ W, τ w = w ↔ w ∈ V
  center_mul_self : ∀ z ∈ zIn W, z * z = 1
  mul_self_mem : ∀ w ∈ W, w * w ∈ zIn W
  center_comm_mem : ∀ z ∈ zIn W, z⁻¹ * τ z ∈ zIn V
  exists_center_comm : ∀ v ∈ zIn V, ∃ z ∈ zIn W, v = z⁻¹ * τ z
  comm_mem : ∀ w ∈ W, w⁻¹ * τ w ∈ ⁅W, W⁆ ⊔ V
  le_closure : ⁅W, W⁆ ⊔ V ≤ closure {x | ∃ w ∈ W, x = w⁻¹ * τ w}
  exists_comm_mod : ∀ v ∈ V, ∃ y ∈ W, v⁻¹ * (y⁻¹ * τ y) ∈ zIn W
  mem_of_comm : ∀ w ∈ W, w⁻¹ * τ w ∈ zIn W → w ∈ V ⊔ zIn W
  mem_center : ∀ v ∈ V, v * v = 1 → v ∈ zIn W

theorem BenderSylowAut.map {X : Type*} [Group X] {τ : MulAut X} {V W : Subgroup X}
    (hX : BenderSylowAut τ V W) {D : Subgroup H} {a : H} (haa : a * a = 1) (haD : a ∉ D)
    (φ : X →* H) (hφ : Function.Injective φ) (hφD : φ.range = D)
    (hτ : ∀ x, a⁻¹ * φ x * a = φ (τ x)) :
    BenderSylow D a (V.map φ) (W.map φ) := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hZW := map_zIn hφ W
  have hZV := map_zIn hφ V
  have hcomm : ⁅W.map φ, W.map φ⁆ ⊔ V.map φ = (⁅W, W⁆ ⊔ V).map φ := by
    rw [Subgroup.map_sup, map_commutator]
  refine
    { mul_self := haa
      not_mem := haD
      le_D := hφD ▸ map_le_range φ W
      isPGroup := hX.isPGroup.map φ
      le := map_mono hX.le
      unique := ?_
      conj_mem := ?_
      inf_centralizer := ?_
      center_mul_self := ?_
      mul_self_mem := ?_
      center_comm_mem := ?_
      exists_center_comm := ?_
      comm_mem := ?_
      le_commutator := ?_
      exists_comm_mod := ?_
      mem_of_comm := ?_
      mem_center := ?_ }
  · intro S hSD hS hVS
    have hS₀ : IsPGroup 2 (S.comap φ) := hS.comap_of_injective φ hφ
    have hVS₀ : V ≤ S.comap φ := fun v hv => hVS (mem_map_of_mem φ hv)
    have hle := hX.unique _ hS₀ hVS₀
    rw [← map_comap_eq_self (hφD ▸ hSD : S ≤ φ.range)]
    exact map_mono hle
  · rintro _ ⟨w, hw, rfl⟩
    rw [hτ]
    exact mem_map_of_mem φ (hX.mem w hw)
  · ext x
    constructor
    · intro hx
      obtain ⟨hxW, hxa⟩ := mem_inf.mp hx
      obtain ⟨w, hw, rfl⟩ := hxW
      have h1 : a⁻¹ * φ w * a = φ w := by
        rw [mul_assoc, mem_centralizer_singleton_iff.mp hxa]
        group
      rw [hτ] at h1
      exact mem_map_of_mem φ ((hX.fixed w hw).mp (hφ h1))
    · rintro ⟨v, hv, rfl⟩
      refine mem_inf.mpr ⟨mem_map_of_mem φ (hX.le hv), ?_⟩
      rw [mem_centralizer_singleton_iff]
      have h1 : φ (τ v) = φ v := by rw [(hX.fixed v (hX.le hv)).mpr hv]
      rw [← hτ] at h1
      calc φ v * a = a * (a⁻¹ * φ v * a) := by group
        _ = a * φ v := by rw [h1]
  · intro z hz
    rw [← hZW] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    rw [← map_mul, hX.center_mul_self z₀ hz₀, map_one]
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← hZW]
    exact mem_map_of_mem φ (hX.mul_self_mem w hw)
  · intro z hz
    rw [← hZW] at hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    rw [hτ, ← map_inv, ← map_mul, ← hZV]
    exact mem_map_of_mem φ (hX.center_comm_mem z₀ hz₀)
  · intro v hv
    rw [← hZV] at hv
    obtain ⟨v₀, hv₀, rfl⟩ := hv
    obtain ⟨z₀, hz₀, hv₀z⟩ := hX.exists_center_comm v₀ hv₀
    refine ⟨φ z₀, hZW ▸ mem_map_of_mem φ hz₀, ?_⟩
    rw [hτ, ← map_inv, ← map_mul, hv₀z]
  · rintro _ ⟨w, hw, rfl⟩
    rw [hτ, ← map_inv, ← map_mul, hcomm]
    exact mem_map_of_mem φ (hX.comm_mem w hw)
  · rw [hcomm]
    refine (map_mono hX.le_closure).trans ?_
    rw [MonoidHom.map_closure, closure_le]
    rintro _ ⟨x, ⟨w, hw, rfl⟩, rfl⟩
    have h1 : φ (w⁻¹ * τ w) = ⁅(φ w)⁻¹, a⁆ := by
      rw [map_mul, map_inv, ← hτ, commutatorElement_def, hainv, inv_inv]
      group
    rw [SetLike.mem_coe, h1]
    exact commutator_mem_commutator (inv_mem (mem_map_of_mem φ hw)) (mem_zpowers a)
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨y, hy, hvy⟩ := hX.exists_comm_mod v hv
    refine ⟨φ y, mem_map_of_mem φ hy, ?_⟩
    rw [hτ, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← hZW]
    exact mem_map_of_mem φ hvy
  · rintro _ ⟨w, hw, rfl⟩ hwc
    rw [hτ, ← map_inv, ← map_mul, ← hZW, mem_map_iff_mem hφ] at hwc
    have := hX.mem_of_comm w hw hwc
    rw [← hZW, ← Subgroup.map_sup]
    exact mem_map_of_mem φ this
  · rintro _ ⟨v, hv, rfl⟩ hvv
    rw [← map_mul, ← map_one φ] at hvv
    rw [← hZW]
    exact mem_map_of_mem φ (hX.mem_center v hv (hφ hvv))

end Ambient

section TwoFactor

variable {A : Type*} [Group A]

@[expose] def diagHom (A : Type*) [Group A] : A →* A × A := (MonoidHom.id A).prod (MonoidHom.id A)

theorem diagHom_apply (x : A) : diagHom A x = (x, x) := rfl

theorem diagHom_injective : Function.Injective (diagHom A) := fun _ _ h => congrArg Prod.fst h

theorem zIn_prod (P Q : Subgroup A) : zIn (P.prod Q) = (zIn P).prod (zIn Q) := by
  ext ⟨z₁, z₂⟩
  simp only [mem_zIn, mem_prod]
  constructor
  · rintro ⟨hc, hz₁, hz₂⟩
    refine ⟨⟨fun w hw => ?_, hz₁⟩, fun w hw => ?_, hz₂⟩
    · have := hc (w, 1) ⟨hw, one_mem Q⟩
      exact congrArg Prod.fst this
    · have := hc (1, w) ⟨one_mem P, hw⟩
      exact congrArg Prod.snd this
  · rintro ⟨⟨hc₁, hz₁⟩, hc₂, hz₂⟩
    refine ⟨fun w hw => ?_, hz₁, hz₂⟩
    obtain ⟨hw₁, hw₂⟩ := hw
    exact Prod.ext (hc₁ w.1 hw₁) (hc₂ w.2 hw₂)

theorem benderSylowAut_swap [Finite A] {P : Subgroup A} (hP : IsPGroup 2 P)
    (hmax : ∀ Q : Subgroup A, IsPGroup 2 Q → P ≤ Q → Q ≤ P)
    (h1 : ∀ z ∈ zIn P, z * z = 1) (h2 : ∀ c ∈ P, c * c ∈ ⁅P, P⁆) (h3 : ⁅P, P⁆ ≤ zIn P)
    (h4 : ∀ v ∈ P, v * v = 1 → v ∈ zIn P) :
    BenderSylowAut (MulEquiv.prodComm : MulAut (A × A)) (P.map (diagHom A)) (P.prod P) := by
  have hZ := zIn_prod P P
  have hZd : zIn (P.map (diagHom A)) = (zIn P).map (diagHom A) :=
    (map_zIn diagHom_injective P).symm
  have hinv : ∀ z ∈ zIn P, z⁻¹ = z := fun z hz => inv_eq_of_mul_eq_one_right (h1 z hz)
  have hsq : ∀ c ∈ P, c * c ∈ zIn P := fun c hc => h3 (h2 c hc)
  have hcomm : ⁅P.prod P, P.prod P⁆ = ⁅P, P⁆.prod ⁅P, P⁆ := commutator_prod_prod P P P P
  refine
    { isPGroup := ?_
      le := ?_
      unique := ?_
      mem := ?_
      fixed := ?_
      center_mul_self := ?_
      mul_self_mem := ?_
      center_comm_mem := ?_
      exists_center_comm := ?_
      comm_mem := ?_
      le_closure := ?_
      exists_comm_mod := ?_
      mem_of_comm := ?_
      mem_center := ?_ }
  · obtain ⟨k, hk⟩ := hP.exists_card_eq
    refine IsPGroup.of_card (n := k + k) ?_
    rw [Nat.card_congr (prodEquiv P P).toEquiv, Nat.card_prod, hk, pow_add]
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨hc, hc⟩
  · intro S hS hPS
    have hS₁ : S.map (MonoidHom.fst A A) ≤ P :=
      hmax _ (hS.map _) (fun c hc => ⟨(c, c), hPS ⟨c, hc, rfl⟩, rfl⟩)
    have hS₂ : S.map (MonoidHom.snd A A) ≤ P :=
      hmax _ (hS.map _) (fun c hc => ⟨(c, c), hPS ⟨c, hc, rfl⟩, rfl⟩)
    exact fun x hx => ⟨hS₁ ⟨x, hx, rfl⟩, hS₂ ⟨x, hx, rfl⟩⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact ⟨hy, hx⟩
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    constructor
    · intro hxy
      have hyx : y = x := congrArg Prod.fst hxy
      exact ⟨x, hx, by rw [diagHom_apply, hyx]⟩
    · rintro ⟨c, hc, hcxy⟩
      rw [diagHom_apply] at hcxy
      rw [← hcxy]
      rfl
  · rintro ⟨z₁, z₂⟩ hz
    rw [hZ] at hz
    exact Prod.ext (h1 z₁ hz.1) (h1 z₂ hz.2)
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := mem_prod.mp hxy
    rw [hZ]
    exact mem_prod.mpr ⟨hsq x hx, hsq y hy⟩
  · rintro ⟨z₁, z₂⟩ hz
    rw [hZ] at hz
    rw [hZd]
    obtain ⟨hz₁, hz₂⟩ := hz
    refine ⟨z₁⁻¹ * z₂, mul_mem (inv_mem hz₁) hz₂, ?_⟩
    change (z₁⁻¹ * z₂, z₁⁻¹ * z₂) = (z₁⁻¹ * z₂, z₂⁻¹ * z₁)
    congr 1
    rw [← hinv _ (mul_mem (inv_mem hz₁) hz₂)]
    group
  · intro v hv
    rw [hZd] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨(1, u), hZ ▸ mem_prod.mpr ⟨one_mem _, hu⟩, ?_⟩
    change (u, u) = (1⁻¹ * u, u⁻¹ * 1)
    rw [inv_one, one_mul, mul_one, hinv u hu]
  · rintro ⟨x, y⟩ hxy
    obtain ⟨hx, hy⟩ := mem_prod.mp hxy
    have hc : x⁻¹ * y ∈ P := mul_mem (inv_mem hx) hy
    have hsplit : ((x, y)⁻¹ * (MulEquiv.prodComm : MulAut (A × A)) (x, y) : A × A) =
        diagHom A (x⁻¹ * y) * (1, ((x⁻¹ * y) * (x⁻¹ * y))⁻¹) := by
      change (x⁻¹ * y, y⁻¹ * x) = (x⁻¹ * y * 1, x⁻¹ * y * ((x⁻¹ * y) * (x⁻¹ * y))⁻¹)
      congr 1 <;> group
    rw [hsplit, hcomm]
    exact mul_mem (mem_sup_right ⟨_, hc, rfl⟩)
      (mem_sup_left (mem_prod.mpr ⟨one_mem _, inv_mem (h2 _ hc)⟩))
  · set C := closure {x : A × A | ∃ w ∈ P.prod P,
      x = w⁻¹ * (MulEquiv.prodComm : MulAut (A × A)) w} with hC
    have hg : ∀ c ∈ P, ((c, c⁻¹) : A × A) ∈ C := fun c hc => subset_closure
      ⟨(1, c), mem_prod.mpr ⟨one_mem _, hc⟩, by
        change (c, c⁻¹) = ((1 : A)⁻¹ * c, c⁻¹ * 1)
        rw [inv_one, one_mul, mul_one]⟩
    have hτC : ∀ x ∈ C, (MulEquiv.prodComm : MulAut (A × A)) x ∈ C := by
      intro x hx
      have hle : C.map (MulEquiv.prodComm : MulAut (A × A)).toMonoidHom ≤ C := by
        rw [hC, MonoidHom.map_closure, closure_le]
        rintro _ ⟨y, ⟨w, hw, rfl⟩, rfl⟩
        refine subset_closure ⟨(MulEquiv.prodComm : MulAut (A × A)) w,
          mem_prod.mpr ⟨(mem_prod.mp hw).2, (mem_prod.mp hw).1⟩, ?_⟩
        obtain ⟨w₁, w₂⟩ := w
        rfl
      exact hle ⟨x, hx, rfl⟩
    have hK₂ : ⁅P, P⁆ ≤ C.comap (MonoidHom.inr A A) := by
      rw [commutator_le]
      intro c hc d hd
      have h1 : ((1, ⁅c, d⁆) : A × A) = (c⁻¹, c⁻¹⁻¹) * (d⁻¹, d⁻¹⁻¹) * (d * c, (d * c)⁻¹) := by
        change ((1 : A), ⁅c, d⁆) = (c⁻¹ * d⁻¹ * (d * c), c⁻¹⁻¹ * d⁻¹⁻¹ * (d * c)⁻¹)
        rw [commutatorElement_def]
        congr 1 <;> group
      change ((1, ⁅c, d⁆) : A × A) ∈ C
      rw [h1]
      exact mul_mem (mul_mem (hg _ (inv_mem hc)) (hg _ (inv_mem hd))) (hg _ (mul_mem hd hc))
    have hK₁ : ∀ x ∈ ⁅P, P⁆, ((x, 1) : A × A) ∈ C := fun x hx =>
      hτC ((1, x) : A × A) (hK₂ hx)
    refine sup_le ?_ ?_
    · rw [hcomm]
      rintro ⟨x, y⟩ hxy
      obtain ⟨hx, hy⟩ := mem_prod.mp hxy
      have : ((x, y) : A × A) = (x, 1) * (1, y) := by
        change (x, y) = (x * 1, 1 * y)
        rw [mul_one, one_mul]
      rw [this]
      exact mul_mem (hK₁ x hx) (hK₂ hy)
    · rintro _ ⟨c, hc, rfl⟩
      have : diagHom A c = (c, c⁻¹) * (1, c * c) := by
        change (c, c) = (c * 1, c⁻¹ * (c * c))
        congr 1 <;> group
      rw [this]
      exact mul_mem (hg c hc) (hK₂ (h2 c hc))
  · rintro _ ⟨c, hc, rfl⟩
    refine ⟨(1, c), mem_prod.mpr ⟨one_mem _, hc⟩, ?_⟩
    rw [hZ]
    change ((c, c)⁻¹ * ((1 : A)⁻¹ * c, c⁻¹ * 1) : A × A) ∈ (zIn P).prod (zIn P)
    refine ⟨?_, ?_⟩
    · change c⁻¹ * (1⁻¹ * c) ∈ zIn P
      rw [inv_one, one_mul, inv_mul_cancel]
      exact one_mem _
    · change c⁻¹ * (c⁻¹ * 1) ∈ zIn P
      rw [mul_one, ← mul_inv_rev]
      exact inv_mem (hsq c hc)
  · rintro ⟨x, y⟩ hxy' hxy
    obtain ⟨hx, hy⟩ := mem_prod.mp hxy'
    rw [hZ] at hxy
    have hc : x⁻¹ * y ∈ zIn P := hxy.1
    have : ((x, y) : A × A) = diagHom A x * (1, x⁻¹ * y) := by
      change (x, y) = (x * 1, x * (x⁻¹ * y))
      congr 1 <;> group
    rw [this, hZ]
    exact mul_mem (mem_sup_left ⟨x, hx, rfl⟩) (mem_sup_right (mem_prod.mpr ⟨one_mem _, hc⟩))
  · rintro _ ⟨c, hc, rfl⟩ hcc
    rw [hZ]
    have hc2 : c * c = 1 := congrArg Prod.fst hcc
    exact mem_prod.mpr ⟨h4 c hc hc2, h4 c hc hc2⟩

variable {H : Type*} [Group H]

theorem benderSylow_of_two_factor [Finite H] {J D : Subgroup H} {a : H} (haa : a * a = 1)
    (hJD : J ≤ D) [Nontrivial J] (haD : ∀ d ∈ D, a⁻¹ * d * a ∈ D) (ψ : D ≃* J × J)
    (hψ₁ : ∀ (j : H) (hjJ : j ∈ J) (hjD : j ∈ D), ψ ⟨j, hjD⟩ = (⟨j, hjJ⟩, ⟨j, hjJ⟩))
    (hψ₂ : ∀ (d : H) (hd : d ∈ D) (hda : a⁻¹ * d * a ∈ D),
      ψ ⟨a⁻¹ * d * a, hda⟩ = (ψ ⟨d, hd⟩).swap)
    {V : Subgroup H} (hV : IsSylowOf 2 V J) (h1 : ∀ z ∈ zIn V, z * z = 1)
    (h2 : ∀ c ∈ V, c * c ∈ ⁅V, V⁆) (h3 : ⁅V, V⁆ ≤ zIn V)
    (h4 : ∀ v ∈ V, v * v = 1 → v ∈ zIn V) :
    BenderSylow D a V
      (((V.subgroupOf J).prod (V.subgroupOf J)).map (D.subtype.comp ψ.symm.toMonoidHom)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := V.subgroupOf J with hPdef
  have hVJ : V ≤ J := hV.le
  have hPV : P.map J.subtype = V := by
    rw [hPdef, subgroupOf_map_subtype, inf_eq_left.mpr hVJ]
  have hinjJ : Function.Injective J.subtype := subtype_injective J
  have hZP : (zIn P).map J.subtype = zIn V := by rw [map_zIn hinjJ, hPV]
  have hCP : ⁅P, P⁆.map J.subtype = ⁅V, V⁆ := by rw [map_commutator, hPV]
  have hP : IsPGroup 2 P := by
    have := hV.isPGroup
    rw [← hPV] at this
    exact this.of_equiv (equivMapOfInjective P J.subtype hinjJ).symm
  have hmax : ∀ Q : Subgroup J, IsPGroup 2 Q → P ≤ Q → Q ≤ P := by
    intro Q hQ hPQ
    have hle : V ≤ Q.map J.subtype := hPV ▸ map_mono hPQ
    have heq := hV.eq_of_le hle (map_subtype_le Q) (hQ.map J.subtype)
    rw [← hPV] at heq
    intro x hx
    have : (x : H) ∈ Q.map J.subtype := ⟨x, hx, rfl⟩
    rw [heq] at this
    obtain ⟨y, hy, hyx⟩ := this
    rwa [← hinjJ hyx]
  have hP1 : ∀ z ∈ zIn P, z * z = 1 := fun z hz => hinjJ (by
    rw [map_mul, map_one]
    exact h1 _ (hZP ▸ mem_map_of_mem _ hz))
  have hP2 : ∀ c ∈ P, c * c ∈ ⁅P, P⁆ := fun c hc => by
    have := h2 _ (hPV ▸ mem_map_of_mem J.subtype hc)
    rw [← map_mul, ← hCP, mem_map_iff_mem hinjJ] at this
    exact this
  have hP3 : ⁅P, P⁆ ≤ zIn P := fun c hc => by
    have := h3 (hCP ▸ mem_map_of_mem J.subtype hc)
    rwa [← hZP, mem_map_iff_mem hinjJ] at this
  have hP4 : ∀ v ∈ P, v * v = 1 → v ∈ zIn P := fun v hv hvv => by
    have := h4 _ (hPV ▸ mem_map_of_mem J.subtype hv) (by
      rw [← map_mul, hvv, map_one])
    rwa [← hZP, mem_map_iff_mem hinjJ] at this
  have hmodel := benderSylowAut_swap hP hmax hP1 hP2 hP3 hP4
  set φ : J × J →* H := D.subtype.comp ψ.symm.toMonoidHom with hφdef
  have hφ : Function.Injective φ := (subtype_injective D).comp ψ.symm.injective
  have hφD : φ.range = D := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (ψ.symm y).2
    · intro hx
      exact ⟨ψ ⟨x, hx⟩, by simp [hφdef]⟩
  have hτ : ∀ x, a⁻¹ * φ x * a = φ ((MulEquiv.prodComm : MulAut (J × J)) x) := by
    intro x
    have hd : φ x ∈ D := (ψ.symm x).2
    have h5 := hψ₂ (φ x) hd (haD _ hd)
    have h6 : (⟨φ x, hd⟩ : D) = ψ.symm x := rfl
    rw [h6, MulEquiv.apply_symm_apply] at h5
    have h7 : (⟨a⁻¹ * φ x * a, haD _ hd⟩ : D) = ψ.symm x.swap := by
      rw [← h5, MulEquiv.symm_apply_apply]
    exact congrArg Subtype.val h7
  have haD' : a ∉ D := by
    intro ha
    obtain ⟨j, hj⟩ := exists_ne (1 : J)
    set d : D := ψ.symm (j, 1) with hd
    have h5 := hψ₂ d d.2 (haD _ d.2)
    have h6 : (⟨a⁻¹ * d * a, haD _ d.2⟩ : D) = (⟨a, ha⟩ : D)⁻¹ * d * ⟨a, ha⟩ := rfl
    rw [h6, map_mul, map_mul, map_inv] at h5
    have h7 : ψ ⟨d, d.2⟩ = (j, 1) := by
      rw [show (⟨d, d.2⟩ : D) = d from rfl, hd, MulEquiv.apply_symm_apply]
    rw [h7] at h5
    have h8 := congrArg Prod.snd h5
    simp only [Prod.snd_mul, Prod.snd_inv, Prod.swap_prod_mk, mul_one, inv_mul_cancel] at h8
    exact hj h8.symm
  have hmap := hmodel.map haa haD' φ hφ hφD hτ
  have hVφ : (P.map (diagHom J)).map φ = V := by
    rw [← hPV, Subgroup.map_map]
    congr 1
    ext x
    change ((ψ.symm (x, x) : D) : H) = x
    rw [← hψ₁ x x.2 (hJD x.2), MulEquiv.symm_apply_apply]
  rwa [hVφ] at hmap

end TwoFactor

end CFSG.LocalAnalysis.EvenBN.TwoF4
