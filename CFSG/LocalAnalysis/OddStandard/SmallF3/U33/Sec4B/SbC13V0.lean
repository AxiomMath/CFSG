module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC13T

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {Y : Subgroup G} {rho v : G}

@[expose] def orbitGrp (rho v : G) : Subgroup G := closure ({v, rho * v * rho⁻¹} : Set G)

private lemma comm_of_mem (hY : CFSG.Open.IsElemAbelian 2 Y) {a b : G} (ha : a ∈ Y)
    (hb : b ∈ Y) : a * b = b * a :=
  congrArg Subtype.val (hY.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

private lemma mem_zpowers_invol {z x : G} (hz : z * z = 1) (hx : x ∈ zpowers z) :
    x = 1 ∨ x = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

private lemma mul_self_eq_inv (hρ3 : rho ^ 3 = 1) : rho * rho = rho⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_three']
  exact hρ3

private lemma inv_mul_inv (hρ3 : rho ^ 3 = 1) : rho⁻¹ * rho⁻¹ = rho := by
  have h3 : rho * rho * rho = 1 := by rw [← pow_three']; exact hρ3
  rw [← mul_self_eq_inv hρ3,
    show (rho * rho) * (rho * rho) = rho * (rho * rho * rho) by group, h3, mul_one]

private lemma rho_conj_inv (hρ3 : rho ^ 3 = 1) (x : G) :
    rho * (rho * x * rho⁻¹) * rho⁻¹ = rho⁻¹ * x * rho := by
  calc rho * (rho * x * rho⁻¹) * rho⁻¹
      = (rho * rho) * x * (rho⁻¹ * rho⁻¹) := by group
    _ = rho⁻¹ * x * rho := by rw [mul_self_eq_inv hρ3, inv_mul_inv hρ3]

private lemma mul_rotate (hY : CFSG.Open.IsElemAbelian 2 Y) {x y z : G} (hx : x ∈ Y)
    (hy : y ∈ Y) (hz : z ∈ Y) : x * y * z = z * x * y := by
  calc x * y * z = x * (y * z) := mul_assoc x y z
    _ = x * (z * y) := by rw [comm_of_mem hY hy hz]
    _ = x * z * y := (mul_assoc x z y).symm
    _ = z * x * y := by rw [comm_of_mem hY hx hz]

private lemma eq_one_of_eq_mul_left {v b : G} (h : b = v * b) : v = 1 := by
  have hh := congrArg (fun z => z * b⁻¹) h
  simp only [mul_assoc, mul_inv_cancel, mul_one] at hh
  exact hh.symm

theorem orbit_norm (hY : CFSG.Open.IsElemAbelian 2 Y) (hρ3 : rho ^ 3 = 1)
    (hρY : ∀ x ∈ Y, rho * x * rho⁻¹ ∈ Y) (hfix : ∀ x ∈ Y, rho * x * rho⁻¹ = x → x = 1)
    (hv : v ∈ Y) : rho⁻¹ * v * rho = v * (rho * v * rho⁻¹) := by
  have hb : rho * v * rho⁻¹ ∈ Y := hρY v hv
  have hc : rho⁻¹ * v * rho ∈ Y := by
    rw [← rho_conj_inv hρ3 v]
    exact hρY _ hb
  have hn : v * (rho * v * rho⁻¹) * (rho⁻¹ * v * rho) ∈ Y :=
    Y.mul_mem (Y.mul_mem hv hb) hc
  have hfixn : rho * (v * (rho * v * rho⁻¹) * (rho⁻¹ * v * rho)) * rho⁻¹ =
      v * (rho * v * rho⁻¹) * (rho⁻¹ * v * rho) := by
    calc rho * (v * (rho * v * rho⁻¹) * (rho⁻¹ * v * rho)) * rho⁻¹
        = (rho * v * rho⁻¹) * (rho * (rho * v * rho⁻¹) * rho⁻¹)
            * (rho * (rho⁻¹ * v * rho) * rho⁻¹) := by group
      _ = (rho * v * rho⁻¹) * (rho⁻¹ * v * rho) * v := by
            rw [rho_conj_inv hρ3 v]
            congr 1
            group
      _ = v * (rho * v * rho⁻¹) * (rho⁻¹ * v * rho) := mul_rotate hY hb hc hv
  have hn1 : v * (rho * v * rho⁻¹) * (rho⁻¹ * v * rho) = 1 := hfix _ hn hfixn
  have hc_eq : rho⁻¹ * v * rho = (v * (rho * v * rho⁻¹))⁻¹ :=
    eq_inv_of_mul_eq_one_right hn1
  rw [hc_eq, mul_inv_rev]
  have hv_inv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hY.2 v hv)
  have hb_inv : (rho * v * rho⁻¹)⁻¹ = rho * v * rho⁻¹ :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hY.2 (rho * v * rho⁻¹) hb)
  rw [hv_inv, hb_inv]
  exact (comm_of_mem hY hv hb).symm

theorem orbit_ne (hfix : ∀ x ∈ Y, rho * x * rho⁻¹ = x → x = 1) (hv : v ∈ Y) (hv1 : v ≠ 1) :
    v ≠ rho * v * rho⁻¹ := by
  intro h
  exact hv1 (hfix v hv h.symm)

theorem mem_orbitGrp_iff (hY : CFSG.Open.IsElemAbelian 2 Y)
    (hρY : ∀ x ∈ Y, rho * x * rho⁻¹ ∈ Y) (hv : v ∈ Y) {x : G} :
    x ∈ orbitGrp rho v ↔ x = 1 ∨ x = v ∨ x = rho * v * rho⁻¹ ∨ x = v * (rho * v * rho⁻¹) := by
  have hb : rho * v * rho⁻¹ ∈ Y := hρY v hv
  have hv2 : v * v = 1 := by simpa [pow_two] using hY.2 v hv
  have hb2 : (rho * v * rho⁻¹) * (rho * v * rho⁻¹) = 1 := by
    simpa [pow_two] using hY.2 (rho * v * rho⁻¹) hb
  have hab : v * (rho * v * rho⁻¹) = (rho * v * rho⁻¹) * v := comm_of_mem hY hv hb
  have h := mem_closure_pair_of_invol (x := x) hv2 hb2 hab
  unfold orbitGrp
  exact h

theorem orbitGrp_props (hY : CFSG.Open.IsElemAbelian 2 Y) (hρ3 : rho ^ 3 = 1)
    (hρY : ∀ x ∈ Y, rho * x * rho⁻¹ ∈ Y) (hfix : ∀ x ∈ Y, rho * x * rho⁻¹ = x → x = 1)
    (hv : v ∈ Y) (hv1 : v ≠ 1) :
    orbitGrp rho v ≤ Y ∧ CFSG.Open.IsElemAbelian 2 (orbitGrp rho v) ∧
      Nat.card ↥(orbitGrp rho v) = 4 := by
  have hb : rho * v * rho⁻¹ ∈ Y := hρY v hv
  have hle : orbitGrp rho v ≤ Y := by
    unfold orbitGrp
    rw [Subgroup.closure_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact hb
  have hEA : CFSG.Open.IsElemAbelian 2 (orbitGrp rho v) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (comm_of_mem hY (hle a.2) (hle b.2))⟩⟩, ?_⟩
    intro x hx
    exact hY.2 x (hle hx)
  refine ⟨hle, hEA, ?_⟩
  have hv2 : v * v = 1 := by simpa [pow_two] using hY.2 v hv
  have hb2 : (rho * v * rho⁻¹) * (rho * v * rho⁻¹) = 1 := by
    simpa [pow_two] using hY.2 (rho * v * rho⁻¹) hb
  have hb_ne_one : (rho * v * rho⁻¹) ≠ 1 := by
    intro h
    apply hv1
    calc v = rho⁻¹ * (rho * v * rho⁻¹) * rho := by group
      _ = 1 := by rw [h]; group
  have hbv : rho * v * rho⁻¹ ∉ zpowers v := by
    intro hmem
    rcases mem_zpowers_invol hv2 hmem with h | h
    · exact hb_ne_one h
    · exact (orbit_ne hfix hv hv1) h.symm
  have hcl : orbitGrp rho v = zpowers v ⊔ zpowers (rho * v * rho⁻¹) := by
    unfold orbitGrp
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  have hcardv : Nat.card ↥(zpowers v) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hY.2 v hv) hv1
  have hcardb : Nat.card ↥(zpowers (rho * v * rho⁻¹)) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hY.2 _ hb) hb_ne_one
  have hcomm_pow : ∀ a ∈ zpowers v, ∀ c ∈ zpowers (rho * v * rho⁻¹), a * c = c * a := by
    intro a ha c hc
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact Commute.zpow_zpow (comm_of_mem hY hv hb) m n
  have hinf : zpowers v ⊓ zpowers (rho * v * rho⁻¹) = ⊥ := by
    by_contra hne
    have hdvd : Nat.card ↥(zpowers v ⊓ zpowers (rho * v * rho⁻¹)) ∣ 2 := by
      rw [← hcardv]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h1 | h2
    · exact hne ((Subgroup.card_eq_one).mp h1)
    · have heq : zpowers v ⊓ zpowers (rho * v * rho⁻¹) = zpowers (rho * v * rho⁻¹) :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h2, hcardb])
      have hle2 : zpowers (rho * v * rho⁻¹) ≤ zpowers v := by
        rw [← heq]
        exact inf_le_left
      exact hbv (hle2 (Subgroup.mem_zpowers _))
  have hprod := card_sup_mul_card_inf hcomm_pow
  rw [← hcl, hcardv, hcardb, hinf, Subgroup.card_bot, mul_one] at hprod
  norm_num at hprod
  exact hprod

theorem orbitGrp_inv (hY : CFSG.Open.IsElemAbelian 2 Y) (hρ3 : rho ^ 3 = 1)
    (hρY : ∀ x ∈ Y, rho * x * rho⁻¹ ∈ Y) (hfix : ∀ x ∈ Y, rho * x * rho⁻¹ = x → x = 1)
    (hv : v ∈ Y) : ∀ x ∈ orbitGrp rho v, rho * x * rho⁻¹ ∈ orbitGrp rho v := by
  intro x hx
  have hb : rho * v * rho⁻¹ ∈ Y := hρY v hv
  rw [mem_orbitGrp_iff hY hρY hv] at hx
  rw [mem_orbitGrp_iff hY hρY hv]
  rcases hx with rfl | rfl | rfl | rfl
  · left
    rw [show rho * 1 * rho⁻¹ = 1 by group]
  · right; right; left; rfl
  · right; right; right
    rw [rho_conj_inv hρ3 v, orbit_norm hY hρ3 hρY hfix hv]
  · right; left
    rw [show rho * (v * (rho * v * rho⁻¹)) * rho⁻¹ = v by
      calc rho * (v * (rho * v * rho⁻¹)) * rho⁻¹
          = (rho * v * rho⁻¹) * (rho * (rho * v * rho⁻¹) * rho⁻¹) := by group
        _ = (rho * v * rho⁻¹) * (rho⁻¹ * v * rho) := by rw [rho_conj_inv hρ3 v]
        _ = (rho * v * rho⁻¹) * (v * (rho * v * rho⁻¹)) := by
              rw [orbit_norm hY hρ3 hρY hfix hv]
        _ = v := by
              rw [← mul_assoc, comm_of_mem hY hb hv, mul_assoc,
                show (rho * v * rho⁻¹) * (rho * v * rho⁻¹) = 1 by
                  simpa [pow_two] using hY.2 (rho * v * rho⁻¹) hb, mul_one]]

theorem orbitGrp_sigma (hY : CFSG.Open.IsElemAbelian 2 Y) (hρ3 : rho ^ 3 = 1)
    (hρY : ∀ x ∈ Y, rho * x * rho⁻¹ ∈ Y) (hfix : ∀ x ∈ Y, rho * x * rho⁻¹ = x → x = 1)
    (hv : v ∈ Y) (hv1 : v ≠ 1) {σ : G} (hσv : σ * v * σ⁻¹ = v)
    (hσρ : σ * rho * σ⁻¹ = rho⁻¹) :
    (∀ x ∈ orbitGrp rho v, σ * x * σ⁻¹ ∈ orbitGrp rho v) ∧
      orbitGrp rho v ⊓ centralizer ({σ} : Set G) = zpowers v := by
  have hb : rho * v * rho⁻¹ ∈ Y := hρY v hv
  have hσb : σ * (rho * v * rho⁻¹) * σ⁻¹ = rho⁻¹ * v * rho := by
    calc σ * (rho * v * rho⁻¹) * σ⁻¹
        = (σ * rho * σ⁻¹) * (σ * v * σ⁻¹) * (σ * rho * σ⁻¹)⁻¹ := by group
      _ = rho⁻¹ * v * (rho⁻¹)⁻¹ := by rw [hσρ, hσv]
      _ = rho⁻¹ * v * rho := by group
  have hσb' : σ * (rho * v * rho⁻¹) * σ⁻¹ = v * (rho * v * rho⁻¹) := by
    rw [hσb, orbit_norm hY hρ3 hρY hfix hv]
  have hσvb : σ * (v * (rho * v * rho⁻¹)) * σ⁻¹ = rho * v * rho⁻¹ := by
    calc σ * (v * (rho * v * rho⁻¹)) * σ⁻¹
        = (σ * v * σ⁻¹) * (σ * (rho * v * rho⁻¹) * σ⁻¹) := by group
      _ = v * (v * (rho * v * rho⁻¹)) := by rw [hσv, hσb']
      _ = rho * v * rho⁻¹ := by
            rw [← mul_assoc, show v * v = 1 by simpa [pow_two] using hY.2 v hv, one_mul]
  constructor
  · intro x hx
    rw [mem_orbitGrp_iff hY hρY hv] at hx
    rw [mem_orbitGrp_iff hY hρY hv]
    rcases hx with rfl | rfl | rfl | rfl
    · left
      rw [show σ * 1 * σ⁻¹ = 1 by group]
    · right; left
      rw [hσv]
    · right; right; right
      rw [hσb']
    · right; right; left
      rw [hσvb]
  · apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxO, hxC⟩ := hx
      have hfixσ : σ * x * σ⁻¹ = x := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hxC
        calc σ * x * σ⁻¹ = (x * σ) * σ⁻¹ := by rw [h]
          _ = x := by group
      rw [mem_orbitGrp_iff hY hρY hv] at hxO
      rcases hxO with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · rw [Subgroup.mem_zpowers_iff]
        exact ⟨1, by simp⟩
      · exfalso
        have h1 : rho * v * rho⁻¹ = v * (rho * v * rho⁻¹) := by
          calc rho * v * rho⁻¹ = σ * (rho * v * rho⁻¹) * σ⁻¹ := hfixσ.symm
            _ = v * (rho * v * rho⁻¹) := hσb'
        exact hv1 (eq_one_of_eq_mul_left h1)
      · exfalso
        have h1 : rho * v * rho⁻¹ = v * (rho * v * rho⁻¹) := by
          calc rho * v * rho⁻¹ = σ * (v * (rho * v * rho⁻¹)) * σ⁻¹ := hσvb.symm
            _ = v * (rho * v * rho⁻¹) := hfixσ
        exact hv1 (eq_one_of_eq_mul_left h1)
    · rw [Subgroup.zpowers_le]
      refine Subgroup.mem_inf.mpr ⟨Subgroup.subset_closure (by simp), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h := congrArg (fun z => z * σ) hσv
      simpa [mul_assoc] using h.symm

theorem orbitGrp_inf (hY : CFSG.Open.IsElemAbelian 2 Y) (hρ3 : rho ^ 3 = 1)
    (hρY : ∀ x ∈ Y, rho * x * rho⁻¹ ∈ Y) (hfix : ∀ x ∈ Y, rho * x * rho⁻¹ = x → x = 1)
    (hv : v ∈ Y) {W : Subgroup G} (hWρ : ∀ x ∈ W, rho * x * rho⁻¹ ∈ W) (hvW : v ∉ W) :
    W ⊓ orbitGrp rho v = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxW, hxO⟩ := hx
  rw [mem_orbitGrp_iff hY hρY hv] at hxO
  rw [Subgroup.mem_bot]
  rcases hxO with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd hxW hvW
  · exfalso
    apply hvW
    have h1 : rho * (rho * v * rho⁻¹) * rho⁻¹ ∈ W := hWρ _ hxW
    have h2 : rho * (rho * (rho * v * rho⁻¹) * rho⁻¹) * rho⁻¹ ∈ W := hWρ _ h1
    have heq : rho * (rho * (rho * v * rho⁻¹) * rho⁻¹) * rho⁻¹ = v := by
      rw [rho_conj_inv hρ3 (rho * v * rho⁻¹)]
      group
    exact heq ▸ h2
  · exfalso
    apply hvW
    have h1 : rho * (v * (rho * v * rho⁻¹)) * rho⁻¹ ∈ W := hWρ _ hxW
    have heq : rho * (v * (rho * v * rho⁻¹)) * rho⁻¹ = v := by
      rw [← orbit_norm hY hρ3 hρY hfix hv]
      group
    exact heq ▸ h1

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
