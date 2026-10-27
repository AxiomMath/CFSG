module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSigBal
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSigCtl
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisNX1

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

namespace SCert.SE

theorem V_inter : ∀ s ∈ Vlist, (s * gen 6 = gen 6 * s ∨ s * invRep 3 = invRep 3 * s) →
    s = 1 ∨ s = gen 0 ∨ s = invRep 1 ∨ s = invRep 1 * gen 0 := by decide +kernel

theorem comm_wit : let p : SE := ⟨0, 1, 0, 0⟩; let q : SE := ⟨4, 0, 0, 0⟩
    p * gen 6 = gen 6 * p ∧ q * gen 6 = gen 6 * q ∧ p * invRep 3 = invRep 3 * p ∧
      q * invRep 3 = invRep 3 * q ∧ p * invRep 1 = invRep 1 * p ∧ q * invRep 1 = invRep 1 * q ∧
      p⁻¹ * q⁻¹ * p * q = gen 0 := by decide

end SCert.SE

variable {G : Type} [Group G] [Finite G]

theorem le_of_zStar {K P : Subgroup G} (hP : IsSylowOf 2 P K) {z : G} (hzP : z ∈ P)
    (hz2 : orderOf z = 2) (hzc : ∀ p ∈ P, z * p = p * z)
    (hiso : ∀ g ∈ K, g⁻¹ * z * g ∈ P → g⁻¹ * z * g = z) {H : Subgroup G}
    (hCH : K ⊓ centralizer ({z} : Set G) ≤ H) (hOH : (pPrimeCore 2 ↥K).map K.subtype ≤ H) :
    K ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := hP.exists_sylow_eq_subgroupOf
  have hmem : ∀ y : ↥K, y ∈ (P₀ : Subgroup ↥K) ↔ (y : G) ∈ P := fun y => by
    rw [hP₀, mem_subgroupOf]
  have hzK : z ∈ K := hP.le hzP
  have hz₀ : (⟨z, hzK⟩ : ↥K) ∈ (P₀ : Subgroup ↥K) := (hmem _).mpr hzP
  have hZ : (⟨⟨z, hzK⟩, hz₀⟩ : (P₀ : Subgroup ↥K)) ∈ Subgroup.center (P₀ : Subgroup ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro p
    have hp : ((p : ↥K) : G) ∈ P := (hmem _).mp p.2
    exact Subtype.ext (Subtype.ext (hzc _ hp).symm)
  have hord : orderOf (⟨⟨z, hzK⟩, hz₀⟩ : (P₀ : Subgroup ↥K)) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hz2]
  have hwc : ∀ g : ↥K, g⁻¹ * ((⟨⟨z, hzK⟩, hz₀⟩ : (P₀ : Subgroup ↥K)) : ↥K) * g ∈
      (P₀ : Subgroup ↥K) → g⁻¹ * ((⟨⟨z, hzK⟩, hz₀⟩ : (P₀ : Subgroup ↥K)) : ↥K) * g =
        ((⟨⟨z, hzK⟩, hz₀⟩ : (P₀ : Subgroup ↥K)) : ↥K) := by
    intro g hg
    exact Subtype.ext (hiso g g.2 ((hmem _).mp hg))
  obtain ⟨hdec, -⟩ := CFSG.Adapters.glauberman_zStar P₀ _ hZ hord hwc
  have hodd : oddCore ↥K = pPrimeCore 2 ↥K := by
    unfold oddCore pPrimeCore
    congr 1
    ext N
    simp [Nat.coprime_two_left]
  intro g hg
  obtain ⟨c, hc, k, hk, hgk⟩ := hdec ⟨g, hg⟩
  have hg' : g = (c : G) * k := congrArg Subtype.val hgk
  rw [hg']
  refine mul_mem (hCH (mem_inf.mpr ⟨c.2, mem_centralizer_singleton_iff.mpr ?_⟩)) (hOH ?_)
  · exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)
  · rw [hodd] at hk
    exact ⟨k, hk, rfl⟩

theorem exists_conj_extremal_in {K P : Subgroup G} {z : G}
    (hP : IsSylowOf 2 P (K ⊓ centralizer ({z} : Set G))) {g w : G} (hg : g ∈ K)
    (hw : g * w * g⁻¹ = z) {p q : G} (hp : p ∈ P) (hq : q ∈ P) (hpw : p * w = w * p)
    (hqw : q * w = w * q) :
    ∃ k ∈ K, k * w * k⁻¹ = z ∧ k * p * k⁻¹ ∈ P ∧ k * q * k⁻¹ ∈ P := by
  set Q := (P ⊓ centralizer ({w} : Set G)).map (MulAut.conj g).toMonoidHom with hQ
  have hPK : P ≤ K := hP.le.trans inf_le_left
  have hQK : Q ≤ K ⊓ centralizer ({z} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hyP, hyw⟩ := mem_inf.mp hy
    refine mem_inf.mpr ⟨mul_mem (mul_mem hg (hPK hyP)) (inv_mem hg), ?_⟩
    rw [mem_centralizer_singleton_iff] at hyw ⊢
    change g * y * g⁻¹ * z = z * (g * y * g⁻¹)
    rw [← hw]
    calc g * y * g⁻¹ * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [hyw]
      _ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
  have hQ2 : IsPGroup 2 Q := (hP.isPGroup.to_le inf_le_left).map _
  obtain ⟨c, hcK, hc⟩ := exists_conj_le_of_isSylowOf hP hQK hQ2
  obtain ⟨hcK', hcz⟩ := mem_inf.mp hcK
  refine ⟨c * g, mul_mem hcK' hg, ?_, ?_, ?_⟩
  · rw [show c * g * w * (c * g)⁻¹ = c * (g * w * g⁻¹) * c⁻¹ by group, hw]
    have := mem_centralizer_singleton_iff.mp hcz
    rw [this]
    group
  · have h := hc _ ⟨p, mem_inf.mpr ⟨hp, mem_centralizer_singleton_iff.mpr hpw⟩, rfl⟩
    rwa [show c * ((MulAut.conj g).toMonoidHom p) * c⁻¹ = c * g * p * (c * g)⁻¹ by
      change c * (g * p * g⁻¹) * c⁻¹ = _
      group] at h
  · have h := hc _ ⟨q, mem_inf.mpr ⟨hq, mem_centralizer_singleton_iff.mpr hqw⟩, rfl⟩
    rwa [show c * ((MulAut.conj g).toMonoidHom q) * c⁻¹ = c * g * q * (c * g)⁻¹ by
      change c * (g * q * g⁻¹) * c⁻¹ = _
      group] at h

omit [Finite G] in
theorem oddCent_zpowers (u : G) : oddCent (zpowers u) =
    (pPrimeCore 2 ↥(centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype := by
  have h : centralizer ((zpowers u : Subgroup G) : Set G) = centralizer ({u} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  have key : ∀ K : Subgroup G, K = centralizer ({u} : Set G) →
      (pPrimeCore 2 ↥K).map K.subtype =
        (pPrimeCore 2 ↥(centralizer ({u} : Set G))).map (centralizer ({u} : Set G)).subtype := by
    rintro K rfl
    rfl
  exact key _ h

namespace GHSylow

variable (D : GHSylow G)

theorem mem_V_of_conj_z_B (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 3, 3, 5, 6, 3, 5].getD i i))
    (h30 : ¬ D.FusN 3 0) (h6 : D.FusN 6 5) {w : G} (hw : w ∈ (D.S : Subgroup G))
    (hwz : ∃ g : G, g⁻¹ * D.z * g = w) : w ∈ D.V := by
  obtain ⟨g, hg⟩ := hwz
  obtain ⟨s, rfl⟩ := D.exists_toG hw
  have hs2 : s * s = 1 := D.toG_injective (by
    rw [map_mul, ← hg, show g⁻¹ * D.z * g * (g⁻¹ * D.z * g) = g⁻¹ * (D.z * D.z) * g by group,
      D.z_mul_z, map_one]
    group)
  have hs1 : s ≠ 1 := fun h => D.z_ne_one (by
    have h' : g⁻¹ * D.z * g = 1 := by rw [hg, h, map_one]
    calc D.z = g * (g⁻¹ * D.z * g) * g⁻¹ := by group
      _ = 1 := by rw [h']; group)
  obtain ⟨-, c, hc⟩ := SE.cls_spec Certificates.certificate22608.1 (s := s)
    (by simp [SE.isInvB, hs2, hs1])
  generalize Fin.ofNat 9 (SE.clsTab s) = i at hc
  have hi0 : D.FusN i 0 := by
    refine ⟨(g * D.toG c)⁻¹, ?_⟩
    rw [show Fin.ofNat 9 i.val = i from Fin.ext (by simp), show SE.invRep (Fin.ofNat 9 0) =
      SE.gen 0 by decide, ← hc, map_mul, map_mul, map_inv, ← hg]
    group
  have hx5 : ¬ D.FusN 5 0 := ((D.not_fusN_x_32) 0 (by simp)).1
  have hV : ∀ r ∈ SE.Vlist, c⁻¹ * s * c = r → D.toG s ∈ D.V := fun r hr h => by
    rw [D.toG_mem_V_iff, show s = (c⁻¹)⁻¹ * r * c⁻¹ by rw [← h]; group]
    exact SE.predV_conj r hr c⁻¹
  fin_cases i
  · exact hV _ (by decide) hc
  · exact hV _ (by decide) hc
  · exact hV _ (by decide) hc
  · exact absurd hi0 h30
  · exact absurd (D.fusN_trans (D.fusN_symm (hP 4 (by decide))) hi0) h30
  · exact absurd hi0 hx5
  · exact absurd (D.fusN_trans (D.fusN_symm h6) hi0) hx5
  · exact absurd (D.fusN_trans (D.fusN_symm (hP 7 (by decide))) hi0) h30
  · exact absurd (D.fusN_trans (D.fusN_symm (hP 8 (by decide))) hi0) hx5

omit [Finite G]
  in
theorem wit_mem :
    D.toG ⟨0, 1, 0, 0⟩ ∈ D.X ∧ D.toG ⟨4, 0, 0, 0⟩ ∈ D.X ∧
      D.toG ⟨0, 1, 0, 0⟩ ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a3a4} : Set G) ∧
      D.toG ⟨4, 0, 0, 0⟩ ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a3a4} : Set G) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := SE.comm_wit
  refine ⟨mem_inf.mpr ⟨D.toG_mem _, ?_⟩, mem_inf.mpr ⟨D.toG_mem _, ?_⟩,
    mem_inf.mpr ⟨D.toG_mem _, ?_⟩, mem_inf.mpr ⟨D.toG_mem _, ?_⟩⟩ <;>
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  · rw [h1]
  · rw [h2]
  · rw [h3]
  · rw [h4]

omit [Finite G]
  in
theorem mem_V_inter {w : G} (hw : w ∈ D.V) (hu : w * D.x = D.x * w ∨ w * D.a3a4 = D.a3a4 * w) :
    w = 1 ∨ w = D.z ∨ w = D.t ∨ w = D.t * D.z := by
  obtain ⟨s, hs, rfl⟩ := D.exists_Vlist hw
  have hu' : s * SE.gen 6 = SE.gen 6 * s ∨ s * SE.invRep 3 = SE.invRep 3 * s := by
    rcases hu with h | h
    · exact Or.inl (D.toG_injective (by rw [map_mul, map_mul]; exact h))
    · exact Or.inr (D.toG_injective (by rw [map_mul, map_mul]; exact h))
  rcases SE.V_inter s hs hu' with rfl | rfl | rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (map_mul _ _ _)))

theorem isolated_z_B (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 3, 3, 5, 6, 3, 5].getD i i))
    (h30 : ¬ D.FusN 3 0) (h6 : D.FusN 6 5) {u : G} (hu : u = D.x ∨ u = D.a3a4)
    (hPu : IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({u} : Set G))
      (centralizer ({u} : Set G)))
    (hcomm : ∀ p ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G),
      ∀ q ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G), ∀ h : G,
        h⁻¹ * D.z * h = p⁻¹ * q⁻¹ * p * q → p⁻¹ * q⁻¹ * p * q = D.z) :
    ∀ g ∈ centralizer ({u} : Set G),
      g⁻¹ * D.z * g ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) → g⁻¹ * D.z * g = D.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg hw
  set w := g⁻¹ * D.z * g with hwdef
  have hwV : w ∈ D.V := D.mem_V_of_conj_z_B hP h30 h6 (mem_inf.mp hw).1 ⟨g, rfl⟩
  have hwu : w * u = u * w := mem_centralizer_singleton_iff.mp (mem_inf.mp hw).2
  have hw' : w * D.x = D.x * w ∨ w * D.a3a4 = D.a3a4 * w := by
    rcases hu with rfl | rfl
    · exact Or.inl hwu
    · exact Or.inr hwu
  have hw1 : w ≠ 1 := fun h => D.z_ne_one (by
    calc D.z = g * w * g⁻¹ := by rw [hwdef]; group
      _ = 1 := by rw [h]; group)
  obtain ⟨hp1, hq1, hp2, hq2⟩ := D.wit_mem
  obtain ⟨-, -, -, -, hpt, hqt, hpq⟩ := SE.comm_wit
  set p : G := D.toG ⟨0, 1, 0, 0⟩
  set q : G := D.toG ⟨4, 0, 0, 0⟩
  have hpP : p ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) := by
    rcases hu with rfl | rfl
    · exact hp1
    · exact hp2
  have hqP : q ∈ (D.S : Subgroup G) ⊓ centralizer ({u} : Set G) := by
    rcases hu with rfl | rfl
    · exact hq1
    · exact hq2
  have hpqz : p⁻¹ * q⁻¹ * p * q = D.z := by
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hpq]
  have hpt' : p * D.t = D.t * p := by rw [← map_mul, ← map_mul, hpt]
  have hqt' : q * D.t = D.t * q := by rw [← map_mul, ← map_mul, hqt]
  have hcz : ∀ c ∈ (D.S : Subgroup G), c * D.z = D.z * c := fun c hc => by
    have h := D.conj_z_S hc
    calc c * D.z = c * (c⁻¹ * D.z * c) := by rw [h]
      _ = D.z * c := by group
  have hPz : IsSylowOf 2 ((D.S : Subgroup G) ⊓ centralizer ({u} : Set G))
      (centralizer ({u} : Set G) ⊓ centralizer ({D.z} : Set G)) :=
    hPu.of_le (le_inf inf_le_right fun c hc =>
      mem_centralizer_singleton_iff.mpr (hcz c (mem_inf.mp hc).1)) inf_le_left
  have key : ∀ w' : G, w' ≠ D.z → (p * w' = w' * p) → (q * w' = w' * q) →
      ¬ ∃ g' ∈ centralizer ({u} : Set G), g' * w' * g'⁻¹ = D.z := by
    rintro w' hw'z hpw hqw ⟨g', hg', hgw⟩
    obtain ⟨k, hk, hkw, hkp, hkq⟩ := exists_conj_extremal_in hPz hg' hgw hpP hqP hpw hqw
    have hkz : k * D.z * k⁻¹ = (k * p * k⁻¹)⁻¹ * (k * q * k⁻¹)⁻¹ * (k * p * k⁻¹) * (k * q * k⁻¹) :=
      by rw [← hpqz]; group
    have h := hcomm _ hkp _ hkq k⁻¹ (by rw [← hkz]; group)
    rw [← hkz] at h
    exact hw'z (by
      calc w' = k⁻¹ * (k * w' * k⁻¹) * k := by group
        _ = k⁻¹ * (k * D.z * k⁻¹) * k := by rw [hkw, h]
        _ = D.z := by group)
  have hg'w : g * w * g⁻¹ = D.z := by rw [hwdef]; group
  rcases D.mem_V_inter hwV hw' with h | h | h | h
  · exact absurd h hw1
  · exact h
  · exact absurd ⟨g, hg, hg'w⟩ (key w (by rw [h]; exact D.z_ne_t.symm) (by rw [h]; exact hpt')
      (by rw [h]; exact hqt'))
  · refine absurd ⟨g, hg, hg'w⟩ (key w ?_ ?_ ?_)
    · rw [h]
      intro htz
      exact D.t_ne_one (by
        calc D.t = D.t * D.z * D.z := by rw [mul_assoc, D.z_mul_z, mul_one]
          _ = 1 := by rw [htz, D.z_mul_z])
    · rw [h, ← mul_assoc, hpt', mul_assoc, hcz p (mem_inf.mp hpP).1, mul_assoc]
    · rw [h, ← mul_assoc, hqt', mul_assoc, hcz q (mem_inf.mp hqP).1, mul_assoc]


theorem N_le_H_B (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hB : D.caseB) : centralizer ({D.x} : Set G) ≤ normalizer (sigW D.V : Set G) := by
  obtain ⟨hP, h30, -, -, ⟨gy, -, hgy⟩, -⟩ := D.fusion_B hC hidx hxa hB
  have h6 : D.FusN 6 5 := D.fusN_of_conj_rep (i := 6) (j := 5)
    (by rw [show SE.invRep 5 = SE.gen 6 by decide]; exact hgy)
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  have hx2 : D.x * D.x = 1 := by rw [← map_mul, show SE.gen 6 * SE.gen 6 = 1 by decide, map_one]
  have hcz : D.x * D.z = D.z * D.x := by
    rw [← map_mul, ← map_mul, show SE.gen 6 * SE.gen 0 = SE.gen 0 * SE.gen 6 by decide]
  have hct : D.x * D.t = D.t * D.x := by
    rw [← map_mul, ← map_mul, show SE.gen 6 * SE.invRep 1 = SE.invRep 1 * SE.gen 6 by decide]
  refine le_of_zStar D.isSylowOf_X (D.toG_mem _ |> fun h => mem_inf.mpr ⟨h,
    mem_centralizer_singleton_iff.mpr hcz.symm⟩)
    (orderOf_eq_prime (by rw [pow_two, D.z_mul_z]) D.z_ne_one)
    (fun p hp => by
      have h := D.conj_z_S (mem_inf.mp hp).1
      calc D.z * p = p * (p⁻¹ * D.z * p) := by group
        _ = p * D.z := by rw [h])
    (D.isolated_z_B hP h30 h6 (Or.inl rfl) D.isSylowOf_X ?_)
    ((inf_le_right).trans (D.M_le_H hC h10 h20)) ?_
  · intro p hp q hq h hh
    obtain ⟨s, rfl⟩ := D.exists_toG (mem_inf.mp hp).1
    obtain ⟨s', rfl⟩ := D.exists_toG (mem_inf.mp hq).1
    have e : D.toG (s⁻¹ * s'⁻¹ * s * s') = h⁻¹ * D.z * h := by
      rw [hh, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc : (s⁻¹ * s'⁻¹ * s * s') * (s⁻¹ * s'⁻¹ * s * s') = 1 := D.toG_injective (by
      rw [map_one, map_mul, e,
        show h⁻¹ * D.z * h * (h⁻¹ * D.z * h) = h⁻¹ * (D.z * D.z) * h by group, D.z_mul_z]
      group)
    have hXs : ∀ {r : SE}, D.toG r ∈ D.X → r ∈ SE.Xlist := fun {r} hr => by
      have := D.eS_mem_Xlist hr
      rwa [D.eS_toG] at this
    rcases SE.commX s (hXs hp) s' (hXs hq) hc with h1 | h1
    · exfalso
      have : h⁻¹ * D.z * h = 1 := by
        rw [hh, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h1, map_one]
      exact D.z_ne_one (by
        calc D.z = h * (h⁻¹ * D.z * h) * h⁻¹ := by group
          _ = 1 := by rw [this]; group)
    · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h1]
  · rw [← oddCent_zpowers]
    exact (D.oddCent_le_W hC h10 h20 hx2 hcz hct).trans le_normalizer

theorem K_le_H_B (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hB : D.caseB) : centralizer ({D.a3a4} : Set G) ≤ normalizer (sigW D.V : Set G) := by
  obtain ⟨hP, h30, -, hsyl, ⟨gy, -, hgy⟩, -⟩ := D.fusion_B hC hidx hxa hB
  have h6 : D.FusN 6 5 := D.fusN_of_conj_rep (i := 6) (j := 5)
    (by rw [show SE.invRep 5 = SE.gen 6 by decide]; exact hgy)
  have h10 : D.FusN 1 0 := hP 1 (by decide)
  have h20 : D.FusN 2 0 := hP 2 (by decide)
  have hu2 : D.a3a4 * D.a3a4 = 1 := by rw [← map_mul, SE.invRep_mul_self', map_one]
  have hcz : D.a3a4 * D.z = D.z * D.a3a4 := by
    rw [← map_mul, ← map_mul, show SE.invRep 3 * SE.gen 0 = SE.gen 0 * SE.invRep 3 by decide]
  have hct : D.a3a4 * D.t = D.t * D.a3a4 := by rw [← map_mul, ← map_mul, SE.a3a4_comm_t]
  refine le_of_zStar hsyl (mem_inf.mpr ⟨D.toG_mem _, mem_centralizer_singleton_iff.mpr hcz.symm⟩)
    (orderOf_eq_prime (by rw [pow_two, D.z_mul_z]) D.z_ne_one)
    (fun p hp => by
      have h := D.conj_z_S (mem_inf.mp hp).1
      calc D.z * p = p * (p⁻¹ * D.z * p) := by group
        _ = p * D.z := by rw [h])
    (D.isolated_z_B hP h30 h6 (Or.inr rfl) hsyl ?_)
    ((inf_le_right).trans (D.M_le_H hC h10 h20)) ?_
  · intro p hp q hq h hh
    obtain ⟨s, rfl⟩ := D.exists_toG (mem_inf.mp hp).1
    obtain ⟨s', rfl⟩ := D.exists_toG (mem_inf.mp hq).1
    have e : D.toG (s⁻¹ * s'⁻¹ * s * s') = h⁻¹ * D.z * h := by
      rw [hh, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hc : (s⁻¹ * s'⁻¹ * s * s') * (s⁻¹ * s'⁻¹ * s * s') = 1 := D.toG_injective (by
      rw [map_one, map_mul, e,
        show h⁻¹ * D.z * h * (h⁻¹ * D.z * h) = h⁻¹ * (D.z * D.z) * h by group, D.z_mul_z]
      group)
    have hTs : ∀ {r : SE}, D.toG r ∈ (D.S : Subgroup G) ⊓ centralizer ({D.a3a4} : Set G) →
        r ∈ SE.Tlist := fun {r} hr => SE.mem_Tlist r (D.toG_injective (by
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.mp (mem_inf.mp hr).2))
    have hnz : ∀ c : SE, ¬ (h⁻¹ * D.z * h = D.toG c ∧ ∃ k : SE, k⁻¹ * c * k = SE.invRep 3) := by
      rintro c ⟨hzc, k, hk⟩
      apply h30
      refine ⟨(h * D.toG k)⁻¹, ?_⟩
      rw [show SE.invRep (Fin.ofNat 9 0) = SE.gen 0 by decide, show Fin.ofNat 9 3 = 3 by decide,
        ← hk, map_mul, map_mul, map_inv, ← hzc]
      group
    rcases SE.commT s (hTs hp) s' (hTs hq) hc with h1 | h1 | h1 | h1
    · exfalso
      have : h⁻¹ * D.z * h = 1 := by rw [← e, h1, map_one]
      exact D.z_ne_one (by
        calc D.z = h * (h⁻¹ * D.z * h) * h⁻¹ := by group
          _ = 1 := by rw [this]; group)
    · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, h1]
    · exact absurd ⟨by rw [← e, h1], 1, by group⟩ (hnz (SE.invRep 3))
    · obtain ⟨k, hk⟩ := SE.a3a4z_conj
      exact absurd ⟨by rw [← e, h1], k, hk⟩ (hnz (SE.invRep 3 * SE.gen 0))
  · rw [← oddCent_zpowers]
    exact (D.oddCent_le_W hC h10 h20 hu2 hcz hct).trans le_normalizer

theorem H_eq_top_B' (hC : GorensteinHaradaThmCInput)
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) (hxa : ¬ ∃ g : G, g⁻¹ * D.x * g = D.a)
    (hB : D.caseB) : normalizer (sigW D.V : Set G) = ⊤ :=
  D.H_eq_top_B hC hidx hxa hB (D.N_le_H_B hC hidx hxa hB) (D.K_le_H_B hC hidx hxa hB)

end GHSylow

end CFSG.ComponentClassification.GHarris
