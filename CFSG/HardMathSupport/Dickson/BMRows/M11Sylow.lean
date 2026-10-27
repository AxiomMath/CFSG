module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
public import Certificates.Certificate17700
public import Certificates.Certificate17701

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Dickson.BMRows.M11

open CFSG.Monster CFSG.Monster.B CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B.Rep4371 CFSG.Monster.Existence CFSG.Monster.Griess
  CFSG.AGLEmbedding.Norton.Gen11 CFSG.AGLEmbedding.Norton.MON11_13 CFSG.CosetTable
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEbar
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem not_two_pow_seven_dvd_card_centralizer_of {x z : G} {S : Subgroup G}
    (hSx : S ≤ Subgroup.centralizer ({x} : Set G)) (hS : Nat.card S = 2 ^ 6) (hzS : z ∈ S)
    (hz1 : z ≠ 1) (hzc : ∀ w ∈ S, z * w = w * z)
    (hZ : ∀ y ∈ S, (∀ w ∈ S, y * w = w * y) → y = 1 ∨ y = z)
    (hD : Nat.card (Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :
      Subgroup G) ∣ 2 ^ 6 * 33) :
    ¬ 2 ^ 7 ∣ Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  intro h7
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({x} : Set G) with hC
  have hS' : Nat.card (S.subgroupOf C) = 2 ^ 6 := by
    rw [← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSx).toEquiv
  obtain ⟨K', hK', hSK'⟩ := Sylow.exists_subgroup_card_pow_succ (n := 6) h7 hS'
  set K := K'.map C.subtype with hKdef
  have hK : Nat.card K = 128 := by
    rw [show (128 : ℕ) = 2 ^ (6 + 1) by norm_num, ← hK']
    exact Nat.card_congr (K'.equivMapOfInjective C.subtype C.subtype_injective).symm.toEquiv
  have hKC : K ≤ C := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hSK : S ≤ K := fun s hs => ⟨⟨s, hSx hs⟩, hSK' (Subgroup.mem_subgroupOf.2 hs), rfl⟩
  have hidx : (S.subgroupOf K).index = 2 := by
    have h1 := (S.subgroupOf K).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hS, hK] at h1
    omega
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  have hconj : ∀ k ∈ K, ∀ w ∈ S, k * w * k⁻¹ ∈ S := fun k hk w hw =>
    Subgroup.mem_subgroupOf.1 (hnorm.conj_mem ⟨w, hSK hw⟩ (Subgroup.mem_subgroupOf.2 hw) ⟨k, hk⟩)
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := by
    intro k hk
    have hy : k * z * k⁻¹ ∈ S := hconj k hk z hzS
    have hyc : ∀ w ∈ S, k * z * k⁻¹ * w = w * (k * z * k⁻¹) := by
      intro w hw
      have h1 := hzc _ (hconj k⁻¹ (K.inv_mem hk) w hw)
      calc k * z * k⁻¹ * w = k * (z * (k⁻¹ * w * k⁻¹⁻¹)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * w * k⁻¹⁻¹) * z) * k⁻¹ := by rw [h1]
        _ = w * (k * z * k⁻¹) := by group
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hZ _ hy hyc with h | h
    · exact absurd (conj_eq_one_iff.1 h) hz1
    · calc k * z = k * z * k⁻¹ * k := by group
        _ = z * k := by rw [h]
  have hdvd := (Subgroup.card_dvd_of_le (le_inf hKz hKC)).trans hD
  rw [hK] at hdvd
  norm_num at hdvd

theorem card_centralizer_dvd_mul_of {H Q : Type*} [Group H] [Group Q] [Finite H]
    (K : Subgroup H) [K.Normal] (e : H ⧸ K ≃* Q) (x : H) {a b : ℕ}
    (hK : Nat.card (K ⊓ Subgroup.centralizer ({x} : Set H) : Subgroup H) ∣ a)
    (hQ : Nat.card (Subgroup.centralizer ({e (QuotientGroup.mk x)} : Set Q)) ∣ b) :
    Nat.card (Subgroup.centralizer ({x} : Set H)) ∣ a * b := by
  rw [card_centralizer_eq_mul K e x]
  exact Nat.mul_dvd_mul hK ((Subgroup.card_dvd_of_le (range_centMap_le K e x)).trans hQ)

end Generic

@[expose] def m11Perm : Fin 4 → Equiv.Perm (Fin 12)
  | 0 => List.formPerm [0, 2, 1, 3] * List.formPerm [6, 7, 9, 11]
  | 1 => List.formPerm [0, 3, 1, 2] * List.formPerm [4, 10, 8, 5]
  | 2 => List.formPerm [0, 2] * List.formPerm [1, 3] * List.formPerm [4, 7] *
      List.formPerm [5, 6] * List.formPerm [8, 11] * List.formPerm [9, 10]
  | 3 => List.formPerm [0, 3] * List.formPerm [1, 2] * List.formPerm [4, 5] *
      List.formPerm [6, 7] * List.formPerm [8, 10] * List.formPerm [9, 11]

theorem m11Perm_relators : ∀ w ∈ m11Rels,
    (w.map fun l => cond l.2 (m11Perm l.1) (m11Perm l.1)⁻¹).prod = 1 := by
  decide +kernel

@[expose] noncomputable def m11PermHom : PG 4 m11Rels →* Equiv.Perm (Fin 12) :=
  PresentedGroup.toGroup (f := m11Perm) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    exact m11Perm_relators w hw)

theorem m11PermHom_of (i : Fin 4) : m11PermHom (PresentedGroup.of i) = m11Perm i := by
  rw [m11PermHom, PresentedGroup.toGroup.of]

@[expose] def m11Word {H : Type*} [Group H] (g : Fin 4 → H)
    (x : Fin 4 × Fin 4 × Fin 2 × Fin 2) : H :=
  g 0 ^ (x.1 : ℕ) * g 1 ^ (x.2.1 : ℕ) * g 2 ^ (x.2.2.1 : ℕ) * g 3 ^ (x.2.2.2 : ℕ)

theorem map_m11Word {H K : Type*} [Group H] [Group K] (f : H →* K) (g : Fin 4 → H)
    (x : Fin 4 × Fin 4 × Fin 2 × Fin 2) : f (m11Word g x) = m11Word (fun i => f (g i)) x := by
  simp only [m11Word, map_mul, map_pow]

@[expose] def m11Idx : List (Fin 4 × Fin 4 × Fin 2 × Fin 2) :=
  (List.finRange 4).flatMap fun i => (List.finRange 4).flatMap fun j =>
    (List.finRange 2).flatMap fun k => (List.finRange 2).map fun l => (i, j, k, l)

theorem mem_m11Idx (x : Fin 4 × Fin 4 × Fin 2 × Fin 2) : x ∈ m11Idx := by
  obtain ⟨i, j, k, l⟩ := x
  simp [m11Idx]

@[expose] def m11Sig : List (Fin 12 × Fin 12 × Fin 12) :=
  [(0, 2, 4), (3, 1, 5), (2, 0, 7), (1, 3, 6), (3, 0, 10), (1, 2, 4), (0, 3, 7), (2, 1, 6),
    (1, 3, 8), (2, 0, 10), (3, 1, 7), (0, 2, 6), (2, 1, 5), (0, 3, 8), (1, 2, 7), (3, 0, 6),
    (2, 1, 4), (0, 3, 5), (1, 2, 9), (3, 0, 7), (0, 2, 10), (3, 1, 4), (2, 0, 9), (1, 3, 7),
    (3, 0, 8), (1, 2, 10), (0, 3, 9), (2, 1, 7), (1, 3, 5), (2, 0, 8), (3, 1, 9), (0, 2, 7),
    (1, 3, 4), (2, 0, 5), (3, 1, 11), (0, 2, 9), (2, 1, 10), (0, 3, 4), (1, 2, 11), (3, 0, 9),
    (0, 2, 8), (3, 1, 10), (2, 0, 11), (1, 3, 9), (3, 0, 5), (1, 2, 8), (0, 3, 11), (2, 1, 9),
    (3, 0, 4), (1, 2, 5), (0, 3, 6), (2, 1, 11), (1, 3, 10), (2, 0, 4), (3, 1, 6), (0, 2, 11),
    (2, 1, 8), (0, 3, 10), (1, 2, 6), (3, 0, 11), (0, 2, 5), (3, 1, 8), (2, 0, 6), (1, 3, 11)]

theorem m11Sig_eq : m11Idx.map (fun x => (m11Word m11Perm x 0, m11Word m11Perm x 2,
    m11Word m11Perm x 4)) = m11Sig := by
  decide +kernel

theorem m11Sig_nodup : m11Sig.Nodup := by
  decide +kernel

theorem m11Word_perm_injective : Function.Injective (m11Word m11Perm) := by
  intro x y h
  have hnd : (m11Idx.map fun x => (m11Word m11Perm x 0, m11Word m11Perm x 2,
      m11Word m11Perm x 4)).Nodup := by
    rw [m11Sig_eq]
    exact m11Sig_nodup
  exact List.inj_on_of_nodup_map hnd (mem_m11Idx x) (mem_m11Idx y) (by rw [h])

theorem m11Perm_center : ∀ x ∈ m11Idx,
    (∀ i, m11Word m11Perm x * m11Perm i = m11Perm i * m11Word m11Perm x) →
      x = (0, 0, 0, 0) ∨ x = (2, 2, 0, 0) := by
  decide +kernel

theorem m11Perm_z_comm : ∀ i, m11Word m11Perm (2, 2, 0, 0) * m11Perm i =
    m11Perm i * m11Word m11Perm (2, 2, 0, 0) := by
  decide +kernel

@[expose] noncomputable def m11PG (x : Fin 4 × Fin 4 × Fin 2 × Fin 2) : PG 4 m11Rels :=
  m11Word PresentedGroup.of x

theorem m11PermHom_m11PG (x : Fin 4 × Fin 4 × Fin 2 × Fin 2) :
    m11PermHom (m11PG x) = m11Word m11Perm x := by
  rw [m11PG, map_m11Word]
  simp only [m11PermHom_of]

theorem m11PG_injective : Function.Injective m11PG := fun x y h =>
  m11Word_perm_injective (by rw [← m11PermHom_m11PG, ← m11PermHom_m11PG, h])

@[expose] noncomputable def m11Z : PG 4 m11Rels := m11PG (2, 2, 0, 0)

section Card


theorem finite_card_m11PG : Finite (PG 4 m11Rels) ∧ Nat.card (PG 4 m11Rels) ≤ 64 :=
  Certificates.certificate17700

theorem card_m11PG : Nat.card (PG 4 m11Rels) = 64 := by
  haveI := finite_card_m11PG.1
  have h := Nat.card_le_card_of_injective m11PG m11PG_injective
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin] at h
  have := finite_card_m11PG.2
  omega

theorem m11PG_bijective : Function.Bijective m11PG := by
  haveI := finite_card_m11PG.1
  refine (Nat.bijective_iff_injective_and_card m11PG).2 ⟨m11PG_injective, ?_⟩
  rw [card_m11PG]
  simp

theorem m11PermHom_injective : Function.Injective m11PermHom := by
  intro g h hgh
  obtain ⟨x, rfl⟩ := m11PG_bijective.2 g
  obtain ⟨y, rfl⟩ := m11PG_bijective.2 h
  rw [m11PermHom_m11PG, m11PermHom_m11PG] at hgh
  rw [m11Word_perm_injective hgh]

theorem m11Z_comm (g : PG 4 m11Rels) : m11Z * g = g * m11Z := by
  have hgen : ∀ i, PresentedGroup.of i ∈ Subgroup.centralizer ({m11Z} : Set (PG 4 m11Rels)) := by
    intro i
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply m11PermHom_injective
    rw [map_mul, map_mul, m11PermHom_of, m11Z, m11PermHom_m11PG]
    exact (m11Perm_z_comm i).symm
  have htop : Subgroup.centralizer ({m11Z} : Set (PG 4 m11Rels)) = ⊤ := by
    rw [eq_top_iff, ← PresentedGroup.closure_range_of
      {r : FreeGroup (Fin 4) | r ∈ m11Rels.map FreeGroup.mk}, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hgen i
  have hg : g ∈ Subgroup.centralizer ({m11Z} : Set (PG 4 m11Rels)) := htop ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_singleton_iff.1 hg).symm

theorem m11PG_center {g : PG 4 m11Rels} (hg : ∀ h, g * h = h * g) : g = 1 ∨ g = m11Z := by
  obtain ⟨x, rfl⟩ := m11PG_bijective.2 g
  have hx : ∀ i, m11Word m11Perm x * m11Perm i = m11Perm i * m11Word m11Perm x := by
    intro i
    rw [← m11PermHom_m11PG, ← m11PermHom_of, ← map_mul, ← map_mul, hg]
  rcases m11Perm_center x (mem_m11Idx x) hx with rfl | rfl
  · left
    simp [m11PG, m11Word]
  · right
    rfl

theorem isPGroup_m11PG : IsPGroup 2 (PG 4 m11Rels) :=
  IsPGroup.of_card (n := 6) (by rw [card_m11PG]; norm_num)

end Card

theorem m11Rels_of {H : Type*} [Group H] {g : Fin 4 → H} {w : H} (ha : g 0 * g 0 = w)
    (hw : w * w = 1) (hs : g 2 * g 2 = 1) (hu : g 3 * g 3 = 1) (hb : g 1 = g 2 * (g 0 * g 2))
    (hab : g 0 * g 1 = g 1 * g 0) (haua : g 0 * (g 3 * g 0) = g 3)
    (hsu : g 3 * g 2 = g 2 * g 3) :
    ∀ r ∈ m11Rels, (r.map fun l => cond l.2 (g l.1) (g l.1)⁻¹).prod = 1 := by
  have hss : ∀ X, g 2 * (g 2 * X) = X := fun X => by rw [← mul_assoc, hs, one_mul]
  have huu : ∀ X, g 3 * (g 3 * X) = X := fun X => by rw [← mul_assoc, hu, one_mul]
  have hww : ∀ X, w * (w * X) = X := fun X => by rw [← mul_assoc, hw, one_mul]
  have haa : ∀ X, g 0 * (g 0 * X) = w * X := fun X => by rw [← mul_assoc, ha]
  have hus : ∀ X, g 3 * (g 2 * X) = g 2 * (g 3 * X) := fun X => by
    rw [← mul_assoc, hsu, mul_assoc]
  have hauaX : ∀ X, g 0 * (g 3 * (g 0 * X)) = g 3 * X := fun X => by
    rw [← mul_assoc, ← mul_assoc, mul_assoc (g 0), haua]
  have hs' : (g 2)⁻¹ = g 2 := inv_eq_of_mul_eq_one_right hs
  have hu' : (g 3)⁻¹ = g 3 := inv_eq_of_mul_eq_one_right hu
  intro r hr
  simp only [m11Rels, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, cond_true, cond_false,
      mul_one]
  · rw [← mul_assoc, ha, hw]
  · rw [hb]
    simp only [mul_assoc, hss, haa, hww, hs]
  · exact hs
  · exact hu
  · rw [hab]
    group
  · rw [hb]
    group
  · rw [haua, hu]
  · rw [hb]
    simp only [mul_assoc, hus, hss, hauaX, huu, hs, hu, hsu]
  · rw [hs', hu', hus, hss, hu]

@[expose] def m11pU : Model.Pauli := Model.Pauli.mul (false, 1557, 3617) (false, 0, 3079)

@[expose] def m11pC : Model.Pauli := Model.Pauli.mul (true, 2030, 2897) (false, 0, 1247)

section Gmat


theorem gw_m11uW : gw m11uW = rhoG m11pU := gw_two_rho _ _

theorem gw_m11cW : gw m11cW = rhoG m11pC := gw_two_rho _ _

theorem gw_m11bW : gw m11bW = gw e0W * (gw m11aW * gw e0W) := by
  rw [m11bW, gw_append, gw_append]

theorem m11_pauli_facts : gw m11uW * gw m11uW = 1 ∧ gw m11cW * gw m11cW = xGmat ∧
    gw m11uW * gw e0W = gw e0W * gw m11uW := by
  rw [gw_m11uW, gw_m11cW, gw_e0W]
  refine ⟨?_, ?_, ?_⟩
  · rw [← rhoG_mul, show Model.Pauli.mul m11pU m11pU = (false, 0, 0) by decide, rhoG_one]
  · rw [← rhoG_mul, show Model.Pauli.mul m11pC m11pC = (true, 0, 0) by decide,
      rhoG_z_eq_xGmat]
  · rw [← rhoG_mul, ← rhoG_mul, show Model.Pauli.mul pE m11pU = Model.Pauli.mul m11pU pE
      by decide]

theorem m11_word_facts :
    gw m11aW * gw m11aW = gw wW ∧ gw m11bW * gw m11aW = gw m11cW ∧
      gw m11aW * gw m11bW = gw m11cW ∧ gw m11aW * (gw m11uW * gw m11aW) = gw m11uW ∧
      gw gen11W0 * gw m11aW = gw m11aW * gw gen11W0 ∧
      gw gen11W0 * gw m11uW = gw m11uW * gw gen11W0 := by
  have h : agreeAll m11Pairs = true := Certificates.certificate17701
  have hp := agreeAll_sound h
  have p : ∀ i, (hi : i < m11Pairs.length) → gw (m11Pairs[i]).1 = gw (m11Pairs[i]).2 :=
    fun i hi => hp _ (List.getElem_mem hi)
  have p0 := p 0 (by decide)
  have p1 := p 1 (by decide)
  have p2 := p 2 (by decide)
  have p3 := p 3 (by decide)
  have p4 := p 4 (by decide)
  have p5 := p 5 (by decide)
  simp only [m11Pairs, List.getElem_cons_zero, List.getElem_cons_succ, gw_append]
    at p0 p1 p2 p3 p4 p5
  exact ⟨p0, p1, p2, p3, p4, p5⟩

@[expose] noncomputable def m11Gen : Fin 4 → Gmat
  | 0 => gw m11aW
  | 1 => gw m11bW
  | 2 => gw e0W
  | 3 => gw m11uW

theorem m11Gen_relators : ∀ r ∈ m11Rels,
    (r.map fun l => cond l.2 (m11Gen l.1) (m11Gen l.1)⁻¹).prod = 1 := by
  obtain ⟨ha, hba, hab, haua, -, -⟩ := m11_word_facts
  obtain ⟨hu, -, hsu⟩ := m11_pauli_facts
  exact m11Rels_of (g := m11Gen) ha w_facts.1 e0_facts.1 hu gw_m11bW (hab.trans hba.symm) haua hsu

@[expose] noncomputable def m11GmatHom : PG 4 m11Rels →* Gmat :=
  PresentedGroup.toGroup (f := m11Gen) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [FreeGroup.lift_mk]
    exact m11Gen_relators w hw)

theorem m11GmatHom_of (i : Fin 4) : m11GmatHom (PresentedGroup.of i) = m11Gen i := by
  rw [m11GmatHom, PresentedGroup.toGroup.of]

theorem m11GmatHom_m11Z : m11GmatHom m11Z = xGmat := by
  obtain ⟨-, hba, hab, -, -, -⟩ := m11_word_facts
  obtain ⟨-, hc, -⟩ := m11_pauli_facts
  have hcomm : gw m11aW * gw m11bW = gw m11bW * gw m11aW := hab.trans hba.symm
  rw [m11Z, m11PG, map_m11Word]
  show m11GmatHom (PresentedGroup.of 0) ^ 2 * m11GmatHom (PresentedGroup.of 1) ^ 2 *
    m11GmatHom (PresentedGroup.of 2) ^ 0 * m11GmatHom (PresentedGroup.of 3) ^ 0 = xGmat
  rw [m11GmatHom_of, m11GmatHom_of, pow_zero, pow_zero, mul_one, mul_one]
  show gw m11aW ^ 2 * gw m11bW ^ 2 = xGmat
  calc gw m11aW ^ 2 * gw m11bW ^ 2 = gw m11aW * (gw m11aW * gw m11bW) * gw m11bW := by
        simp only [pow_two, mul_assoc]
    _ = gw m11aW * (gw m11bW * gw m11aW) * gw m11bW := by rw [hcomm]
    _ = gw m11aW * gw m11bW * (gw m11aW * gw m11bW) := by simp only [mul_assoc]
    _ = xGmat := by rw [hab, hc]


theorem m11GmatHom_injective : Function.Injective m11GmatHom := by
  haveI := finite_card_m11PG.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := isPGroup_m11PG.isNilpotent
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hne
  obtain ⟨⟨g, hg⟩, hg1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  obtain ⟨hgk, hgc⟩ := Subgroup.mem_inf.1 hg
  have hg1' : g ≠ 1 := fun h => hg1 (Subtype.ext h)
  rcases m11PG_center (fun h => (Subgroup.mem_center_iff.1 hgc h).symm) with h | h
  · exact hg1' h
  · rw [h, MonoidHom.mem_ker, m11GmatHom_m11Z] at hgk
    exact xGmat_ne_one hgk

@[expose] noncomputable def m11S : Subgroup Gmat := m11GmatHom.range

theorem card_m11S : Nat.card m11S = 2 ^ 6 := by
  rw [m11S, ← Nat.card_congr (MonoidHom.ofInjective m11GmatHom_injective).toEquiv, card_m11PG]
  norm_num

theorem m11S_le_centralizer : m11S ≤ Subgroup.centralizer ({gw gen11W0} : Set Gmat) := by
  obtain ⟨-, -, -, -, hxa, hxu⟩ := m11_word_facts
  have hxs : gw gen11W0 * gw e0W = gw e0W * gw gen11W0 := eleven_data_facts.2.2.2.2.2.2.2.1
  rw [m11S, MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of
    {r : FreeGroup (Fin 4) | r ∈ m11Rels.map FreeGroup.mk}, MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, m11GmatHom_of, Subgroup.mem_centralizer_singleton_iff]
  fin_cases i
  · exact hxa.symm
  · change gw m11bW * gw gen11W0 = gw gen11W0 * gw m11bW
    have h1 : Commute (gw gen11W0) (gw e0W) := hxs
    have h2 : Commute (gw gen11W0) (gw m11aW) := hxa
    rw [gw_m11bW]
    exact (h1.mul_right (h2.mul_right h1)).eq.symm
  · exact hxs.symm
  · exact hxu.symm

theorem xGmat_mem_m11S : xGmat ∈ m11S := ⟨m11Z, m11GmatHom_m11Z⟩

theorem xGmat_comm_m11S : ∀ w ∈ m11S, xGmat * w = w * xGmat := by
  rintro _ ⟨h, rfl⟩
  rw [← m11GmatHom_m11Z, ← map_mul, ← map_mul, m11Z_comm]

theorem m11S_center : ∀ y ∈ m11S, (∀ w ∈ m11S, y * w = w * y) → y = 1 ∨ y = xGmat := by
  rintro _ ⟨g, rfl⟩ hg
  have hc : ∀ h, g * h = h * g := fun h => m11GmatHom_injective (by
    rw [map_mul, map_mul]
    exact hg _ ⟨h, rfl⟩)
  rcases m11PG_center hc with rfl | rfl
  · exact Or.inl (map_one _)
  · exact Or.inr m11GmatHom_m11Z

theorem card_centralizer_x11H_dvd :
    Nat.card (Subgroup.centralizer ({x11H} : Set (cent xGmat))) ∣ 2 ^ 6 * 33 := by
  obtain ⟨e⟩ := twoB_xGmat.2.2.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := ((pCore_isPGroup (p := 2) (G := cent xGmat)).to_le
    (inf_le_left : pCore 2 (cent xGmat) ⊓ Subgroup.centralizer ({x11H} : Set (cent xGmat)) ≤
      pCore 2 (cent xGmat))).exists_card_eq
  have hle := card_pCore_inf_centralizer_x11_le
  rw [hn] at hle
  have hn5 : n ≤ 5 := by
    by_contra h
    have h6 : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact absurd (h6.trans hle) (by norm_num)
  have h32 : Nat.card (pCore 2 (cent xGmat) ⊓ Subgroup.centralizer ({x11H} : Set (cent xGmat)) :
      Subgroup (cent xGmat)) ∣ 2 ^ 5 := by
    rw [hn]
    exact Nat.pow_dvd_pow 2 hn5
  have h := @card_centralizer_dvd_mul_of (cent xGmat) CFSG.Blueprint.NativeSporadic.Co1 _
    Units.instGroup _ (pCore 2 (cent xGmat)) _ e x11H _ _ h32
    (card_centralizer_image_dvd e orderOf_x11H)
  rwa [show (2 : ℕ) ^ 5 * 66 = 2 ^ 6 * 33 by norm_num] at h

theorem card_centralizer_xGmat_inf_x11_dvd :
    Nat.card (Subgroup.centralizer ({xGmat} : Set Gmat) ⊓
      Subgroup.centralizer ({gw gen11W0} : Set Gmat) : Subgroup Gmat) ∣ 2 ^ 6 * 33 := by
  have hcard : Nat.card (Subgroup.centralizer ({xGmat} : Set Gmat) ⊓
      Subgroup.centralizer ({gw gen11W0} : Set Gmat) : Subgroup Gmat) =
      Nat.card (Subgroup.centralizer ({x11H} : Set (cent xGmat))) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩,
          Subgroup.mem_centralizer_singleton_iff.2
            (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2))⟩
        invFun := fun y => ⟨y.1.1, Subgroup.mem_inf.2 ⟨y.1.2,
          Subgroup.mem_centralizer_singleton_iff.2
            (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 y.2))⟩⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
  rw [hcard]
  exact card_centralizer_x11H_dvd

theorem not_two_pow_seven_dvd_card_centralizer_x11 :
    ¬ 2 ^ 7 ∣ Nat.card (Subgroup.centralizer ({gw gen11W0} : Set Gmat)) :=
  not_two_pow_seven_dvd_card_centralizer_of m11S_le_centralizer card_m11S xGmat_mem_m11S
    xGmat_ne_one xGmat_comm_m11S m11S_center card_centralizer_xGmat_inf_x11_dvd

end Gmat

end CFSG.HardMathSupport.Dickson.BMRows.M11
