module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Step8
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step11
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step10
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3S7Syl

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {z : G} {L S : Subgroup G}

section Certified


theorem S7Config.not_le (hI : S7Inputs) (h : S7Config G z L)
    (hS : IsSylowOf 2 S (centralizer {z})) : ¬ S ≤ L := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hI.solomon G h.nonab h.kProper h.notCat z h.hz L h.hL h.hzL 3 1 Nat.prime_three
    (by norm_num) h.hcov (by norm_num) (h.characteristic hI) (h.Q_eq hI) (h.commutator_le hI)
    (fun x hx => h.conj_iff hI hx) (hS.isPGroup.toSylow (h.not_dvd_index hI hS))

namespace Step6Three

variable (d : Step6Three z L S)

theorem exists_pi (hI : S7Inputs) (h : S7Config G z L) (hS : IsSylowOf 2 S (centralizer {z})) :
    ∃ π : G, π * d.z₁ * π⁻¹ = z ∧ (∀ t ∈ S ⊓ centralizer {d.z₁},
      π * t * π⁻¹ ∈ S ⊓ centralizer {d.z₁}) ∧
      ∀ t ∈ S ⊓ centralizer {d.z₁}, t⁻¹ * (π * t * π⁻¹) ∈ L := by
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := S ⊓ centralizer {d.z₁} with hTdef
  set M := centralizer ({z} : Set G) ⊓ centralizer {d.z₁} with hMdef
  have hT : IsSylowOf 2 T M := d.hT
  have hTS : T ≤ S := inf_le_left
  have hSH : S ≤ centralizer {z} := hS.le
  have hTH : T ≤ centralizer {z} := hTS.trans hSH
  have hTp : IsPGroup 2 T := hS.isPGroup.to_le hTS
  have hz₁H : d.z₁ ∈ centralizer ({z} : Set G) := h.hL.1 d.hz₁L
  have hc : z * d.z₁ = d.z₁ * z := (mem_centralizer_singleton_iff.mp hz₁H).symm
  have hzz : z * z = 1 := by rw [← sq, ← h.hz, pow_orderOf_eq_one]
  have hz₁z₁ : d.z₁ * d.z₁ = 1 := by rw [← sq, ← d.hz₁, pow_orderOf_eq_one]
  have hne : d.z₁ ≠ z := fun he => d.hz₁Z (by
    have h1 : (⟨d.z₁, d.hz₁L⟩ : ↥L) = ⟨z, h.hzL⟩ := Subtype.ext he
    rw [h1]
    exact mk_mem_center_of_mem_center (mem_center_of_le_centralizer h.hL.1 h.hzL))
  have hzz₁ : orderOf (z * d.z₁) = 2 := F3.orderOf_mul_of_commute h.hz d.hz₁ hc hne
  have hzz₁L : z * d.z₁ ∈ L := mul_mem h.hzL d.hz₁L
  have hzz₁Z : (QuotientGroup.mk (⟨z * d.z₁, hzz₁L⟩ : ↥L) : Bar L) ∉ center (Bar L) := by
    intro hcen
    apply d.hz₁Z
    have h1 : (QuotientGroup.mk (⟨d.z₁, d.hz₁L⟩ : ↥L) : Bar L) =
        (QuotientGroup.mk ⟨z, h.hzL⟩)⁻¹ * QuotientGroup.mk ⟨z * d.z₁, hzz₁L⟩ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp
    rw [h1]
    exact mul_mem (inv_mem (mk_mem_center_of_mem_center
      (mem_center_of_le_centralizer h.hL.1 h.hzL))) hcen
  obtain ⟨a, haL, ha⟩ := F3S7.spinSeven_conj_of_involution_three h.hcov d.hz₁L hzz₁L d.hz₁ hzz₁
    d.hz₁Z hzz₁Z
  have haH : a ∈ centralizer ({z} : Set G) := h.hL.1 haL
  have haz : a * z * a⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp haH, mul_inv_cancel_right]
  have hMz : ∀ {c : G}, c * z * c⁻¹ = z → c * d.z₁ * c⁻¹ = z * d.z₁ →
      M.map (MulAut.conj c).toMonoidHom = M := by
    intro c h1 h2
    rw [hMdef, map_conj_centralizer_inf, h1, h2, T23.centralizer_inf_mul]
  obtain ⟨k₁, hk₁M, hn₁, hn₂⟩ := exists_conj_normalizes hT (hMz haz ha)
  set n := k₁⁻¹ * a with hn
  have hk₁H : k₁ ∈ centralizer ({z} : Set G) := (mem_inf.mp hk₁M).1
  have hnH : n ∈ centralizer ({z} : Set G) := mul_mem (inv_mem hk₁H) haH
  have hk₁z₁ : k₁ * d.z₁ = d.z₁ * k₁ := mem_centralizer_singleton_iff.mp (mem_inf.mp hk₁M).2
  have hk₁z : k₁ * z = z * k₁ := mem_centralizer_singleton_iff.mp hk₁H
  have hnz : n * z * n⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp hnH, mul_inv_cancel_right]
  have hnz₁ : n * d.z₁ * n⁻¹ = z * d.z₁ := by
    calc n * d.z₁ * n⁻¹ = k₁⁻¹ * (a * d.z₁ * a⁻¹) * k₁ := by rw [hn]; group
      _ = k₁⁻¹ * (z * d.z₁) * k₁ := by rw [ha]
      _ = z * d.z₁ := conj_eq_of_commute (commute_mul' hk₁z hk₁z₁)
  have hπz : (a * d.b) * z * (a * d.b)⁻¹ = d.z₁ := by
    calc (a * d.b) * z * (a * d.b)⁻¹ = a * (d.b * z * d.b⁻¹) * a⁻¹ := by group
      _ = (a * z * a⁻¹) * (a * d.z₁ * a⁻¹) := by rw [d.hbz]; group
      _ = d.z₁ := by rw [haz, ha, ← mul_assoc, hzz, one_mul]
  have hπz₁ : (a * d.b) * d.z₁ * (a * d.b)⁻¹ = z * d.z₁ := by
    calc (a * d.b) * d.z₁ * (a * d.b)⁻¹ = a * (d.b * d.z₁ * d.b⁻¹) * a⁻¹ := by group
      _ = z * d.z₁ := by rw [d.hbz₁, ha]
  have hMπ : M.map (MulAut.conj (a * d.b)).toMonoidHom = M := by
    rw [hMdef, map_conj_centralizer_inf, hπz, hπz₁, hc, T23.centralizer_inf_mul, inf_comm]
  obtain ⟨k₂, hk₂M, hπ₁, hπ₂⟩ := exists_conj_normalizes hT hMπ
  set π := k₂⁻¹ * (a * d.b) with hπ
  have hk₂z₁ : k₂ * d.z₁ = d.z₁ * k₂ := mem_centralizer_singleton_iff.mp (mem_inf.mp hk₂M).2
  have hk₂z : k₂ * z = z * k₂ := mem_centralizer_singleton_iff.mp (mem_inf.mp hk₂M).1
  have hπz' : π * z * π⁻¹ = d.z₁ := by
    calc π * z * π⁻¹ = k₂⁻¹ * ((a * d.b) * z * (a * d.b)⁻¹) * k₂ := by rw [hπ]; group
      _ = d.z₁ := by rw [hπz]; exact conj_eq_of_commute hk₂z₁
  have hπz₁' : π * d.z₁ * π⁻¹ = z * d.z₁ := by
    calc π * d.z₁ * π⁻¹ = k₂⁻¹ * ((a * d.b) * d.z₁ * (a * d.b)⁻¹) * k₂ := by rw [hπ]; group
      _ = z * d.z₁ := by rw [hπz₁]; exact conj_eq_of_commute (commute_mul' hk₂z hk₂z₁)
  have hK1 : ∀ k ∈ centralizer ({z} : Set G), (∀ t ∈ T, k * t * k⁻¹ ∈ T) →
      ∀ t ∈ T, t⁻¹ * (k * t * k⁻¹) ∈ L := fun k hk hkT t ht =>
    h.inv_mul_conj_mem hI hTH hTp ht hk (hkT t ht)
  have hcl := h.closure_inf_eq hI d.hz₁L d.hz₁ d.hz₁Z hT
  have hK4 : ∀ l ∈ T ⊓ L, π * l * π⁻¹ ∈ L := by
    have hle : closure {x | x ∈ T ⊓ L ∧ x * x = 1} ≤
        (L.map (MulAut.conj π⁻¹).toMonoidHom) := by
      rw [closure_le]
      rintro x ⟨hxTL, hx2⟩
      obtain ⟨hxT, hxL⟩ := mem_inf.mp hxTL
      have hπx : π * x * π⁻¹ ∈ L := by
        by_cases hx1 : x = 1
        · rw [hx1, mul_one, mul_inv_cancel]
          exact one_mem L
        · have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hx2]) hx1
          obtain ⟨g, hg⟩ := (h.conj_iff hI (hTH hxT)).mpr ⟨hxL, hxo⟩
          have hπxT : π * x * π⁻¹ ∈ T := hπ₁ x hxT
          exact ((h.conj_iff hI (hTH hπxT)).mp ⟨π * g, by rw [← hg]; group⟩).1
      rw [SetLike.mem_coe, mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
      exact hπx
    intro l hl
    have h0 : l ∈ closure {x | x ∈ T ⊓ L ∧ x * x = 1} := by rw [hcl]; exact hl
    have h1 := hle h0
    rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv] at h1
    exact h1
  have hn₁' : ∀ t ∈ T, n * t * n⁻¹ ∈ T := hn₁
  have hn₂' : ∀ t ∈ T, n⁻¹ * t * n⁻¹⁻¹ ∈ T := fun t ht => by
    rw [inv_inv]
    exact hn₂ t ht
  have hnz' : n⁻¹ * z * n = z := by
    calc n⁻¹ * z * n = n⁻¹ * (n * z * n⁻¹) * n := by rw [hnz]
      _ = z := by group
  have hnz₁' : n⁻¹ * d.z₁ * n = z * d.z₁ := by
    have h1 : d.z₁ = z * (n * d.z₁ * n⁻¹) := by rw [hnz₁, ← mul_assoc, hzz, one_mul]
    calc n⁻¹ * d.z₁ * n = n⁻¹ * (z * (n * d.z₁ * n⁻¹)) * n := by rw [← h1]
      _ = (n⁻¹ * z * n) * d.z₁ := by group
      _ = z * d.z₁ := by rw [hnz']
  have hz₁zz₁ : d.z₁ * (z * d.z₁) = z := by
    rw [← mul_assoc, ← hc, mul_assoc, hz₁z₁, mul_one]
  set w := n * π * n⁻¹ * π with hw
  have hwz : w * z * w⁻¹ = z := by
    calc w * z * w⁻¹ = n * (π * (n⁻¹ * (π * z * π⁻¹) * n) * π⁻¹) * n⁻¹ := by rw [hw]; group
      _ = n * (π * (z * d.z₁) * π⁻¹) * n⁻¹ := by rw [hπz', hnz₁']
      _ = n * ((π * z * π⁻¹) * (π * d.z₁ * π⁻¹)) * n⁻¹ := by group
      _ = z := by rw [hπz', hπz₁', hz₁zz₁, hnz]
  have hwH : w ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc w * z = w * z * w⁻¹ * w := by group
      _ = z * w := by rw [hwz]
  have hwT : ∀ t ∈ T, w * t * w⁻¹ ∈ T := by
    intro t ht
    rw [show w * t * w⁻¹ = n * (π * (n⁻¹ * (π * t * π⁻¹) * n⁻¹⁻¹) * π⁻¹) * n⁻¹ by rw [hw]; group]
    exact hn₁' _ (hπ₁ _ (hn₂' _ (hπ₁ t ht)))
  refine ⟨π * π, ?_, fun t ht => ?_, fun t ht => ?_⟩
  · calc π * π * d.z₁ * (π * π)⁻¹ = π * (π * d.z₁ * π⁻¹) * π⁻¹ := by group
      _ = π * (z * d.z₁) * π⁻¹ := by rw [hπz₁']
      _ = (π * z * π⁻¹) * (π * d.z₁ * π⁻¹) := by group
      _ = z := by rw [hπz', hπz₁', hz₁zz₁]
  · rw [show π * π * t * (π * π)⁻¹ = π * (π * t * π⁻¹) * π⁻¹ by group]
    exact hπ₁ _ (hπ₁ t ht)
  · set a₁ := π * t * π⁻¹ with ha₁
    have ha₁T : a₁ ∈ T := hπ₁ t ht
    set a₂ := n⁻¹ * a₁ * n⁻¹⁻¹ with ha₂
    have ha₂T : a₂ ∈ T := hn₂' a₁ ha₁T
    have hR₁ : a₁⁻¹ * a₂ ∈ L := hK1 n⁻¹ (inv_mem hnH) hn₂' a₁ ha₁T
    have hR₂ : (π * a₁ * π⁻¹)⁻¹ * (π * a₂ * π⁻¹) ∈ L := by
      rw [show (π * a₁ * π⁻¹)⁻¹ * (π * a₂ * π⁻¹) = π * (a₁⁻¹ * a₂) * π⁻¹ by group]
      exact hK4 _ (mem_inf.mpr ⟨mul_mem (inv_mem ha₁T) ha₂T, hR₁⟩)
    set a₃ := π * a₂ * π⁻¹ with ha₃
    have ha₃T : a₃ ∈ T := hπ₁ a₂ ha₂T
    have hR₃ : a₃⁻¹ * (n * a₃ * n⁻¹) ∈ L := hK1 n hnH hn₁' a₃ ha₃T
    have hR₄ : t⁻¹ * (w * t * w⁻¹) ∈ L := hK1 w hwH hwT t ht
    have hwt : w * t * w⁻¹ = n * a₃ * n⁻¹ := by
      rw [hw, ha₃, ha₂, ha₁]
      group
    rw [hwt] at hR₄
    have h1 := mul_mem (mul_mem hR₄ (inv_mem hR₃)) (inv_mem hR₂)
    rwa [show t⁻¹ * (n * a₃ * n⁻¹) * (a₃⁻¹ * (n * a₃ * n⁻¹))⁻¹ *
      ((π * a₁ * π⁻¹)⁻¹ * a₃)⁻¹ = t⁻¹ * (π * a₁ * π⁻¹) by group,
      show π * a₁ * π⁻¹ = π * π * t * (π * π)⁻¹ by rw [ha₁]; group] at h1

end Step6Three

theorem S7Config.mem_of_barAction_mem_range (hI : S7Inputs) (h : S7Config G z L) {x : G}
    (hxN : x ∈ normalizer (L : Set G)) (hxH : x ∈ centralizer ({z} : Set G)) {n : ℕ}
    (hxn : x ^ 2 ^ n = 1)
    (hx : barAction L ⟨x, hxN⟩ ∈ (MulAut.conj : Bar L →* MulAut (Bar L)).range) : x ∈ L := by
  obtain ⟨w, hw⟩ := hx
  obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective w
  have hlN : l ∈ normalizer (L : Set G) := le_normalizer hl
  have h1 : barAction L ⟨l, hlN⟩ = MulAut.conj (QuotientGroup.mk ⟨l, hl⟩ : Bar L) :=
    barAction_of_mem L ⟨l, hl⟩ hlN
  have h2 : barAction L ⟨x * l⁻¹, mul_mem hxN (inv_mem hlN)⟩ = 1 := by
    have h3 : (⟨x * l⁻¹, mul_mem hxN (inv_mem hlN)⟩ : ↥(normalizer (L : Set G))) =
        ⟨x, hxN⟩ * (⟨l, hlN⟩)⁻¹ := rfl
    rw [h3, map_mul, map_inv, ← hw, h1, mul_inv_cancel]
  have hK : x * l⁻¹ ∈ coreActionKernel L :=
    (mem_ker_barAction L _).mp (MonoidHom.mem_ker.mpr h2)
  have hQ : x * l⁻¹ ∈ centralizer ({z} : Set G) ⊓ coreActionKernel L :=
    mem_inf.mpr ⟨mul_mem hxH (inv_mem (h.hL.1 hl)), hK⟩
  rw [h.Q_eq hI] at hQ
  have hle : (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔
      zpowers z ≤ (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ L :=
    sup_le_sup_left (zpowers_le.mpr h.hzL) _
  have h4 := mul_mem (hle hQ) (mem_sup_right hl)
  rw [inv_mul_cancel_right] at h4
  have := h.normal hI
  exact mem_of_mem_sup_of_two_pow h.hL.1 h4 hxn

theorem S7Config.exists_V (hI : S7Inputs) (h : S7Config G z L)
    (hS : IsSylowOf 2 S (centralizer {z})) :
    ∃ V : Subgroup G, V ≤ S ∧ S ⊓ L ≤ V ∧ (∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V) ∧
      (∀ v ∈ V, ∀ w ∈ V, v ∉ L → w ∉ L → v⁻¹ * w ∈ L) ∧
      (∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ V) ∧
      (∀ v ∈ V, v * v ∈ zpowers z → v ∈ L) ∧
      ((∃ s ∈ S, s ∉ V) → ∃ x ∈ S, x ∉ L ∧ x * x ∈ zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut (Bar L)) := finite_mulAut' _
  set H := centralizer ({z} : Set G) with hH
  have hLn := h.normal hI
  have hHN : H ≤ normalizer (L : Set G) := (normal_subgroupOf_iff_le_normalizer h.hL.1).mp hLn
  set ρ : ↥H →* MulAut (Bar L) := (barAction L).comp (Subgroup.inclusion hHN) with hρ
  have hρapp : ∀ x : ↥H, ρ x = barAction L ⟨x, hHN x.2⟩ := fun x => rfl
  set Inn := (MulAut.conj : Bar L →* MulAut (Bar L)).range with hInn
  set C := (⊤ : Subgroup ↥H).map ρ with hC
  set P := (S.subgroupOf H).map ρ with hP
  have hS2 : ∀ s ∈ S, ∃ n : ℕ, s ^ 2 ^ n = 1 := fun s hs => by
    obtain ⟨n, hn⟩ := hS.isPGroup ⟨s, hs⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hρL : ∀ x : ↥H, (x : G) ∈ L → ρ x ∈ Inn := fun x hx =>
    ⟨QuotientGroup.mk ⟨x, hx⟩, (barAction_of_mem L ⟨x, hx⟩ (hHN x.2)).symm⟩
  have hInnL : ∀ x : ↥H, (x : G) ∈ S → ρ x ∈ Inn → (x : G) ∈ L := fun x hxS hx => by
    obtain ⟨n, hn⟩ := hS2 _ hxS
    exact h.mem_of_barAction_mem_range hI (hHN x.2) x.2 hn hx
  have hρP : ∀ s (hs : s ∈ S), ρ ⟨s, hS.le hs⟩ ∈ P := fun s hs => ⟨⟨s, hS.le hs⟩, hs, rfl⟩
  have hInnC : Inn ≤ C := by
    rintro _ ⟨w, rfl⟩
    obtain ⟨⟨l, hl⟩, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨⟨l, h.hL.1 hl⟩, mem_top _, barAction_of_mem L ⟨l, hl⟩ (hHN (h.hL.1 hl))⟩
  have hS' : IsSylowOf 2 (S.subgroupOf H) ⊤ := (isSylowOf_map_subtype_iff H).mp (by
    rwa [subgroupOf_map_subtype, map_subtype_top', inf_eq_left.mpr hS.le])
  have hPC : IsSylowOf 2 P C := IsSylowOf.map ρ hS'
  obtain ⟨W, -, hW2, hW3, hW4, hW5, hW6, hW7⟩ := hI.u4 (Bar L) 3 1 Nat.prime_three
    (by norm_num) h.hcov C P hInnC (isSylowIn_iff_isSylowOf.mpr hPC)
  set V := (W.comap ρ).map H.subtype ⊓ S with hV
  have hmemV : ∀ {s : G} (hs : s ∈ S), s ∈ V ↔ ρ ⟨s, hS.le hs⟩ ∈ W := by
    intro s hs
    constructor
    · intro hsV
      obtain ⟨y, hy, hys⟩ := (mem_inf.mp hsV).1
      have h1 : (⟨s, hS.le hs⟩ : ↥H) = y := Subtype.ext hys.symm
      rw [h1]
      exact hy
    · intro hρs
      exact mem_inf.mpr ⟨⟨⟨s, hS.le hs⟩, hρs, rfl⟩, hs⟩
  have hVS : V ≤ S := inf_le_right
  have hz1 : ∀ hzH : z ∈ H, ρ ⟨z, hzH⟩ = 1 := fun hzH => by
    rw [hρapp]
    exact MonoidHom.mem_ker.mp ((mem_ker_barAction L _).mpr (mem_inf.mp h.mem_Q).2)
  refine ⟨V, hVS, fun s hs => ?_, fun s hs v hv => ?_, fun v hv w hw hvL hwL => ?_, ?_,
    fun v hv hv2 => ?_, ?_⟩
  ·
    obtain ⟨hsS, hsL⟩ := mem_inf.mp hs
    exact (hmemV hsS).mpr (hW2 (mem_inf.mpr ⟨hρP s hsS, hρL _ hsL⟩))
  ·
    have hvS := hVS hv
    have hsvS : s * v * s⁻¹ ∈ S := mul_mem (mul_mem hs hvS) (inv_mem hs)
    refine (hmemV hsvS).mpr ?_
    have h1 : (⟨s * v * s⁻¹, hS.le hsvS⟩ : ↥H) =
        ⟨s, hS.le hs⟩ * ⟨v, hS.le hvS⟩ * (⟨s, hS.le hs⟩)⁻¹ := rfl
    rw [h1, map_mul, map_mul, map_inv]
    exact hW3 _ (hρP s hs) _ ((hmemV hvS).mp hv)
  ·
    have hvS := hVS hv
    have hwS := hVS hw
    have hvwS : v⁻¹ * w ∈ S := mul_mem (inv_mem hvS) hwS
    refine hInnL ⟨v⁻¹ * w, hS.le hvwS⟩ hvwS ?_
    have h1 : (⟨v⁻¹ * w, hS.le hvwS⟩ : ↥H) = (⟨v, hS.le hvS⟩)⁻¹ * ⟨w, hS.le hwS⟩ := rfl
    rw [h1, map_mul, map_inv]
    exact hW4 _ ((hmemV hvS).mp hv) _ ((hmemV hwS).mp hw)
      (fun h2 => hvL (hInnL _ hvS h2)) (fun h2 => hwL (hInnL _ hwS h2))
  ·
    obtain ⟨b, ⟨y, hy, rfl⟩, hb⟩ := hW5
    refine ⟨y, hy, fun t ht => ?_⟩
    obtain ⟨k, hk⟩ := hb _ (hρP t ht)
    have hkS : ((y : G) ^ k)⁻¹ * t ∈ S := mul_mem (inv_mem (zpow_mem hy k)) ht
    refine ⟨k, (hmemV hkS).mpr ?_⟩
    have h1 : (⟨((y : G) ^ k)⁻¹ * t, hS.le hkS⟩ : ↥H) = (y ^ k)⁻¹ * ⟨t, hS.le ht⟩ :=
      Subtype.ext (by simp)
    rw [h1, map_mul, map_inv, map_zpow]
    exact hk
  ·
    have hvS := hVS hv
    refine hInnL ⟨v, hS.le hvS⟩ hvS (hW6 _ ((hmemV hvS).mp hv) ?_)
    have h1 : ρ ⟨v, hS.le hvS⟩ * ρ ⟨v, hS.le hvS⟩ = ρ ⟨v * v, mul_mem (hS.le hvS) (hS.le hvS)⟩ :=
      (map_mul ρ _ _).symm
    rw [h1]
    have hzz : z * z = 1 := by rw [← sq, ← h.hz, pow_orderOf_eq_one]
    rcases T23.eq_one_or_eq_of_mem_zpowers hzz hv2 with h2 | h2
    · have h3 : (⟨v * v, mul_mem (hS.le hvS) (hS.le hvS)⟩ : ↥H) = 1 := Subtype.ext h2
      rw [h3, map_one]
    · have h3 : (⟨v * v, mul_mem (hS.le hvS) (hS.le hvS)⟩ : ↥H) =
          ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ := Subtype.ext h2
      rw [h3, hz1]
  ·
    rintro ⟨s, hs, hsV⟩
    obtain ⟨_, ⟨y, hy, rfl⟩, hyInn, hy2⟩ :=
      hW7 ⟨ρ ⟨s, hS.le hs⟩, hρP s hs, fun h1 => hsV ((hmemV hs).mpr h1)⟩
    refine ⟨y, hy, fun h1 => hyInn (hρL y h1), ?_⟩
    rw [← h.inf_Q_eq hI hS]
    have h1 : ρ (y * y) = 1 := by rw [map_mul, hy2]
    rw [hρapp] at h1
    exact mem_inf.mpr ⟨mul_mem hy hy, mem_inf.mpr ⟨(y * y).2,
      (mem_ker_barAction L _).mp (MonoidHom.mem_ker.mpr h1)⟩⟩

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
