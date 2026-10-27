module

public import CFSG.ClassicalInvolution.Asc77.AscT7F2Bsub
public import CFSG.ClassicalInvolution.Asc77.AscT7G2Data

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace T7QEng

open T7F2 T7G2 T7DR

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {R R' : Subgroup G} {z t' : G}

structure Frame (S : Sylow 2 G) (R R' : Subgroup G) (z t' : G) : Prop where
  hzR : IsUniqueInvolution R z
  hqR : IsQuatSub R
  hcomm : Commutes R R'
  hRS : R ≤ (S : Subgroup G)
  ht'S : t' ∈ (S : Subgroup G)
  ht'2 : t' * t' = 1
  ht'R : conjSub t' R = R'
  ht'R' : conjSub t' R' = R
  ht'inv : t'⁻¹ = t'
  conj_R'_of_mem_N : ∀ {n : G}, n ∈ Nsub S R → conjSub n R' = R'
  C'_le_N : Csub S R' ≤ Nsub S R
  N_conj : ∀ {n : G}, n ∈ Nsub S R → t' * n * t'⁻¹ ∈ Nsub S R
  S_cover : ∀ {s : G}, s ∈ (S : Subgroup G) → s ∈ Nsub S R ∨ t' * s ∈ Nsub S R
  conj_mem_RR : ∀ {x : G}, x ∈ (S : Subgroup G) → ∀ {ρ : G}, ρ ∈ R ⊔ R' → x * ρ * x⁻¹ ∈ R ⊔ R'
  inf_R_R'_eq : R ⊓ R' = Subgroup.zpowers z
  eq_one_or_z_of_mem_zpowers : ∀ {w : G}, w ∈ Subgroup.zpowers z → w = 1 ∨ w = z
  struct : Csub S R' = R ∧ Csub S R = R' ∧ R' ⊔ Csub S R' = R ⊔ R' ∧ R ⊔ Csub S R = R ⊔ R' ∧
      (R ⊔ R').relIndex (Nsub S R) = 2
  exists_comm_not_mem : ∀ {m : G}, m ∈ Nsub S R →
      m ∉ R' ⊔ (Nsub S R ⊓ Subgroup.centralizer (R' : Set G)) → ∃ r ∈ R', ⁅m, r⁆ ∉ squaresSub R'
  squaresSub_conj_mem : ∀ {g : G}, (∀ r ∈ R, g * r * g⁻¹ ∈ R') → ∀ {x : G}, x ∈ squaresSub R →
      g * x * g⁻¹ ∈ squaresSub R'

theorem z_eq_pow_gen (hzR : IsUniqueInvolution R z) {a b : G} {n : ℕ} (c : QuatCoord R a b n) :
    z = a ^ (2 ^ n) := by
  have h1 : a ^ (2 ^ n) * a ^ (2 ^ n) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']; exact c.pow_card
  have h2 : a ^ (2 ^ n) ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf (by positivity)
    rw [c.hord]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rcases hzR.unique _ (R.pow_mem c.ha _) h1 with h3 | h3
  · exact absurd h3 h2
  · exact h3.symm

theorem exists_comm_not_mem_R_gen (h : Frame S R R' z t') {s : G} (hsN : s ∈ Nsub S R)
    (hsn : s ∉ R ⊔ R') : ∃ r ∈ R, ⁅s, r⁆ ∉ squaresSub R := by
  obtain ⟨hC', hC, hP', hP, hidx⟩ := h.struct
  have hti := h.ht'inv
  have hm : t' * s * t'⁻¹ ∈ Nsub S R := h.N_conj hsN
  have hmn : t' * s * t'⁻¹ ∉ R' ⊔ (Nsub S R ⊓ Subgroup.centralizer (R' : Set G)) := by
    have heq : Nsub S R ⊓ Subgroup.centralizer (R' : Set G) = Csub S R' := by
      ext x
      constructor
      · rintro ⟨hxN, hxc⟩
        exact mem_Csub.mpr ⟨(mem_Nsub.mp hxN).1,
          fun r hr => Subgroup.mem_centralizer_iff.mp hxc r hr⟩
      · intro hx
        exact ⟨h.C'_le_N hx, Subgroup.mem_centralizer_iff.mpr (mem_Csub.mp hx).2⟩
    rw [heq]
    have hPeq : R' ⊔ Csub S R' = R ⊔ R' := hP'
    rw [hPeq]
    intro hmem
    apply hsn
    have h1 := h.conj_mem_RR h.ht'S hmem
    have e : t' * (t' * s * t'⁻¹) * t'⁻¹ = s := by
      calc t' * (t' * s * t'⁻¹) * t'⁻¹ = (t' * t') * s * (t'⁻¹ * t'⁻¹) := by group
        _ = s := by rw [h.ht'2, hti, h.ht'2]; group
    rw [e] at h1
    exact h1
  obtain ⟨r', hr', hnot⟩ := h.exists_comm_not_mem hm hmn
  have hr : t'⁻¹ * r' * t' ∈ R := by
    have : r' ∈ conjSub t' R := by rw [h.ht'R]; exact hr'
    exact mem_conjSub_iff.mp this
  refine ⟨t'⁻¹ * r' * t', hr, fun hmem => hnot ?_⟩
  have hconjR : ∀ r ∈ R, t' * r * t'⁻¹ ∈ R' := fun r hr => by
    have := conj_mem_conjSub (n := t') hr
    rwa [h.ht'R] at this
  have h1 := h.squaresSub_conj_mem hconjR hmem
  have e : t' * ⁅s, t'⁻¹ * r' * t'⁆ * t'⁻¹ = ⁅t' * s * t'⁻¹, r'⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e] at h1
  exact h1

theorem exists_coord_s_gen (h : Frame S R R' z t') {s : G} (hsN : s ∈ Nsub S R)
    (hsn : s ∉ R ⊔ R') :
    ∃ (a b : G) (n : ℕ) (i m : ℤ), QuatCoord R a b n ∧ Odd i ∧ Odd m ∧
      s * a * s⁻¹ = a ^ i ∧ s * b * s⁻¹ = b * a ^ m := by
  obtain ⟨hsS, hsR⟩ := mem_Nsub.mp hsN
  have hV2 : IsPGroup 2 (Subgroup.zpowers s) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hsS)
  have hVR : ∀ y ∈ Subgroup.zpowers s, conjSub y R = R := fun y hy =>
    (mem_Nsub.mp ((Subgroup.zpowers_le.mpr hsN) hy)).2
  obtain ⟨a, b, n, c, hinv⟩ := T7F2.exists_coord h.hqR h.hzR hV2 hVR
  have hinvs : conjSub s (Subgroup.zpowers a) = Subgroup.zpowers a :=
    hinv s (Subgroup.mem_zpowers s)
  have h1 : s * a * s⁻¹ ∈ Subgroup.zpowers a := by
    have := conj_mem_conjSub (n := s) (Subgroup.mem_zpowers a)
    rwa [hinvs] at this
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hsbR : s * b * s⁻¹ ∈ R := by
    have := conj_mem_conjSub (n := s) c.hb
    rwa [hsR] at this
  have hiodd : Odd i := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨c', hc'⟩ := hev
    have h1 : (s * a * s⁻¹) ^ (2 ^ n) = 1 := by
      rw [← hi, ← zpow_natCast, ← zpow_mul]
      have : a ^ (i * ((2 ^ n : ℕ) : ℤ)) = (a ^ (2 ^ (n + 1))) ^ c' := by
        rw [← zpow_natCast, ← zpow_mul, hc']
        congr 1
        push_cast
        ring
      rw [this, c.pow_card, one_zpow]
    have h2 : (s * a * s⁻¹) ^ (2 ^ n) = s * a ^ (2 ^ n) * s⁻¹ := conj_pow
    have h3 : a ^ (2 ^ n) ≠ 1 := by
      apply pow_ne_one_of_lt_orderOf (by positivity)
      rw [c.hord]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    apply h3
    have h5 : s * a ^ (2 ^ n) * s⁻¹ = 1 := h2 ▸ h1
    calc a ^ (2 ^ n) = s⁻¹ * (s * a ^ (2 ^ n) * s⁻¹) * s := by group
      _ = 1 := by rw [h5]; group
  obtain ⟨m, hm⟩ : ∃ m : ℤ, s * b * s⁻¹ = b * a ^ m := by
    rcases c.cover _ hsbR with ⟨l, hl⟩ | ⟨l, hl⟩
    · exfalso
      apply c.b_not_mem
      have hbe : b = s⁻¹ * a ^ l * s := by rw [← hl]; group
      rw [hbe]
      have hmem : a ^ l ∈ conjSub s (Subgroup.zpowers a) := by
        rw [hinvs]; exact Subgroup.zpow_mem_zpowers a l
      exact mem_conjSub_iff.mp hmem
    · exact ⟨l, hl⟩
  have hmodd : Odd m := by
    by_contra hev
    rw [Int.not_odd_iff_even] at hev
    obtain ⟨r, hr, hnot⟩ := exists_comm_not_mem_R_gen h hsN hsn
    apply hnot
    have ha2 : ∀ j : ℤ, a ^ (2 * j) ∈ squaresSub R := fun j => by
      have := zpow_mem (square_mem_squaresSub c.ha) j
      have e : (a * a) ^ j = a ^ (2 * j) := by
        rw [← pow_two, ← zpow_natCast, ← zpow_mul]
        norm_num
      rwa [e] at this
    obtain ⟨ci, hci⟩ := hiodd
    obtain ⟨cm, hcm⟩ := hev
    rcases c.cover r hr with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · have : ⁅s, a ^ l⁆ = a ^ (2 * (ci * l)) := by
        rw [commutatorElement_def]
        calc s * a ^ l * s⁻¹ * (a ^ l)⁻¹ = (s * a * s⁻¹) ^ l * (a ^ l)⁻¹ := by rw [conj_zpow]
          _ = a ^ (2 * (ci * l)) := by
            rw [← hi, ← zpow_mul, ← zpow_neg, ← zpow_add, hci]
            congr 1
            ring
      rw [this]
      exact ha2 _
    · have : ⁅s, b * a ^ l⁆ = a ^ (2 * (-(cm + ci * l))) := by
        rw [commutatorElement_def]
        calc s * (b * a ^ l) * s⁻¹ * (b * a ^ l)⁻¹
            = (s * b * s⁻¹) * (s * a * s⁻¹) ^ l * (a ^ l)⁻¹ * b⁻¹ := by
              rw [conj_zpow]; group
          _ = b * a ^ m * a ^ (i * l) * (a ^ l)⁻¹ * b⁻¹ := by
              rw [hm, ← hi, ← zpow_mul]
          _ = b * a ^ (m + i * l - l) * b⁻¹ := by group
          _ = a ^ (-(m + i * l - l)) := c.conj_zpow _
          _ = a ^ (2 * (-(cm + ci * l))) := by
              congr 1
              rw [hci, hcm]
              ring
      rw [this]
      exact ha2 _
  exact ⟨a, b, n, i, m, c, hiodd, hmodd, hi.symm, hm⟩

theorem sq_form_gen (h : Frame S R R' z t') {s : G} (hsN : s ∈ Nsub S R) (hst' : s * t' = t' * s)
    {a b : G} {n : ℕ} (c : QuatCoord R a b n) {i m : ℤ} (hi : Odd i) (hm : Odd m)
    (hsa : s * a * s⁻¹ = a ^ i) (hsb : s * b * s⁻¹ = b * a ^ m) :
    ∃ k δ : ℤ, s * s = a ^ k * (t' * a * t'⁻¹) ^ k * a ^ ((2 ^ n : ℤ) * δ) := by
  obtain ⟨hC', hC, hP', hP, hidx⟩ := h.struct
  obtain ⟨hsS, hsR⟩ := mem_Nsub.mp hsN
  have hza := z_eq_pow_gen h.hzR c
  have hs2mem : s * s ∈ R ⊔ R' := (mul_mem_iff_of_relIndex_two hidx hsN hsN).mpr Iff.rfl
  obtain ⟨ρ, hρ, ρ', hρ', hss⟩ := T7F2.Out.exists_mul_of_mem_sup_of_commute h.hcomm hs2mem
  have hρ'1 : s * ρ' * s⁻¹ ∈ R' := by
    have := conj_mem_conjSub (n := s) hρ'
    rwa [h.conj_R'_of_mem_N hsN] at this
  have hsρ : s * ρ * s⁻¹ ∈ R := by
    have := conj_mem_conjSub (n := s) hρ
    rwa [hsR] at this
  have hρa : ρ ∈ Subgroup.zpowers a := by
    by_contra hnot
    obtain ⟨l, hl⟩ : ∃ l : ℤ, ρ = b * a ^ l := by
      rcases c.cover ρ hρ with ⟨l, hl⟩ | ⟨l, hl⟩
      · exact absurd ⟨l, hl.symm⟩ hnot
      · exact ⟨l, hl⟩
    have h1 : s * ρ * s⁻¹ = b * a ^ (m + i * l) := by
      rw [hl]
      calc s * (b * a ^ l) * s⁻¹ = (s * b * s⁻¹) * (s * a * s⁻¹) ^ l := by
            rw [conj_zpow]; group
        _ = b * a ^ m * a ^ (i * l) := by rw [hsb, hsa, ← zpow_mul]
        _ = b * a ^ (m + i * l) := by rw [mul_assoc, ← zpow_add]
    have h2 : (s * ρ * s⁻¹) * (s * ρ' * s⁻¹) = ρ * ρ' := by
      calc (s * ρ * s⁻¹) * (s * ρ' * s⁻¹) = s * (ρ * ρ') * s⁻¹ := by group
        _ = s * (s * s) * s⁻¹ := by rw [hss]
        _ = s * s := by group
      rw [← hss]
    have h3 : ρ⁻¹ * (s * ρ * s⁻¹) = ρ' * (s * ρ' * s⁻¹)⁻¹ := by
      calc ρ⁻¹ * (s * ρ * s⁻¹)
          = ρ⁻¹ * ((s * ρ * s⁻¹) * (s * ρ' * s⁻¹)) * (s * ρ' * s⁻¹)⁻¹ := by group
        _ = ρ⁻¹ * (ρ * ρ') * (s * ρ' * s⁻¹)⁻¹ := by rw [h2]
        _ = ρ' * (s * ρ' * s⁻¹)⁻¹ := by group
    have hmem : ρ⁻¹ * (s * ρ * s⁻¹) ∈ R ⊓ R' :=
      ⟨R.mul_mem (R.inv_mem hρ) hsρ, h3 ▸ R'.mul_mem hρ' (R'.inv_mem hρ'1)⟩
    rw [h.inf_R_R'_eq] at hmem
    have h4' : ρ⁻¹ * (s * ρ * s⁻¹) = a ^ (m + (i - 1) * l) := by
      rw [h1, hl]; group
    obtain ⟨cm, hcm⟩ := hm
    obtain ⟨ci, hci⟩ := hi
    obtain ⟨q, hq⟩ : ∃ q : ℤ, m + (i - 1) * l = 2 * q + 1 :=
      ⟨cm + ci * l, by rw [hcm, hci]; ring⟩
    have h2n : (2 : ℤ) ∣ 2 ^ (n + 1) := dvd_pow_self 2 (Nat.succ_ne_zero n)
    have hd : (2 : ℤ) ∣ m + (i - 1) * l := by
      rcases h.eq_one_or_z_of_mem_zpowers hmem with h5 | h5
      · rw [h4'] at h5
        have : a ^ (m + (i - 1) * l) = a ^ (0 : ℤ) := by rw [h5, zpow_zero]
        rw [c.zpow_eq_iff] at this
        exact dvd_trans h2n (by simpa using this)
      · rw [h4', hza, ← zpow_natCast] at h5
        rw [c.zpow_eq_iff] at h5
        have h6 : (2 : ℤ) ∣ m + (i - 1) * l - ((2 ^ n : ℕ) : ℤ) :=
          dvd_trans h2n h5
        have h7 : (2 : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) := by
          have : ((2 ^ n : ℕ) : ℤ) = 2 * 2 ^ (n - 1) := by
            have := c.hn
            obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
            push_cast; ring
          exact ⟨_, this⟩
        have := dvd_add h6 h7
        simpa using this
    rw [hq] at hd
    omega
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hρa
  have hts' : t' * s * t'⁻¹ = s := by
    calc t' * s * t'⁻¹ = s * t' * t'⁻¹ := by rw [hst']
      _ = s := by group
  have ha'R' : t' * a * t'⁻¹ ∈ R' := by
    have := conj_mem_conjSub (n := t') c.ha
    rwa [h.ht'R] at this
  have hρ''R : t' * ρ' * t'⁻¹ ∈ R := by
    have := conj_mem_conjSub (n := t') hρ'
    rwa [h.ht'R'] at this
  set a' : G := t' * a * t'⁻¹ with ha'def
  have E1 : a' ^ k * (t' * ρ' * t'⁻¹) = a ^ k * ρ' := by
    have e1 : t' * (s * s) * t'⁻¹ = s * s := by
      calc t' * (s * s) * t'⁻¹ = (t' * s * t'⁻¹) * (t' * s * t'⁻¹) := by group
        _ = s * s := by rw [hts']
    rw [hss, ← hk] at e1
    calc a' ^ k * (t' * ρ' * t'⁻¹) = t' * a ^ k * t'⁻¹ * (t' * ρ' * t'⁻¹) := by
          rw [ha'def, conj_zpow]
      _ = t' * (a ^ k * ρ') * t'⁻¹ := by group
      _ = a ^ k * ρ' := e1
  have ha'k : ∀ j : ℤ, a' ^ j ∈ R' := fun j => R'.zpow_mem ha'R' j
  have hak : ∀ j : ℤ, a ^ j ∈ R := fun j => R.zpow_mem c.ha j
  have hX : (t' * ρ' * t'⁻¹) * a ^ (-k) = ρ' * a' ^ (-k) := by
    have e1 : (t' * ρ' * t'⁻¹) * a' ^ k = ρ' * a ^ k := by
      calc (t' * ρ' * t'⁻¹) * a' ^ k = a' ^ k * (t' * ρ' * t'⁻¹) :=
            h.hcomm _ hρ''R _ (ha'k k)
        _ = a ^ k * ρ' := E1
        _ = ρ' * a ^ k := h.hcomm _ (hak k) _ hρ'
    have hc : a ^ (-k) * a' ^ k = a' ^ k * a ^ (-k) := h.hcomm _ (hak (-k)) _ (ha'k k)
    calc (t' * ρ' * t'⁻¹) * a ^ (-k)
        = (t' * ρ' * t'⁻¹) * (a ^ (-k) * a' ^ k) * a' ^ (-k) := by group
      _ = (t' * ρ' * t'⁻¹) * (a' ^ k * a ^ (-k)) * a' ^ (-k) := by rw [hc]
      _ = ((t' * ρ' * t'⁻¹) * a' ^ k) * a ^ (-k) * a' ^ (-k) := by group
      _ = (ρ' * a ^ k) * a ^ (-k) * a' ^ (-k) := by rw [e1]
      _ = ρ' * a' ^ (-k) := by group
  have hmem : ρ' * a' ^ (-k) ∈ Subgroup.zpowers z := by
    rw [← h.inf_R_R'_eq]
    exact ⟨hX ▸ R.mul_mem hρ''R (hak (-k)), R'.mul_mem hρ' (ha'k (-k))⟩
  have hzc : z * a' ^ k = a' ^ k * z := h.hcomm _ h.hzR.mem _ (ha'k k)
  rcases h.eq_one_or_z_of_mem_zpowers hmem with h5 | h5
  · refine ⟨k, 0, ?_⟩
    have : ρ' = a' ^ k := by
      calc ρ' = (ρ' * a' ^ (-k)) * a' ^ k := by group
        _ = a' ^ k := by rw [h5]; group
    rw [hss, ← hk, this]
    simp
  · refine ⟨k, 1, ?_⟩
    have : ρ' = z * a' ^ k := by
      calc ρ' = (ρ' * a' ^ (-k)) * a' ^ k := by group
        _ = z * a' ^ k := by rw [h5]
    have e : a ^ ((2 ^ n : ℤ) * 1) = a ^ (2 ^ n : ℕ) := by
      rw [mul_one, ← zpow_natCast]; push_cast; rfl
    rw [hss, ← hk, this, hzc, hza, e]
    group

theorem closure_eq_S_gen (h : Frame S R R' z t') {s : G} (hsN : s ∈ Nsub S R) (hsn : s ∉ R ⊔ R')
    {a b : G} {n : ℕ} (c : QuatCoord R a b n) :
    Subgroup.closure ({a, b, s, t'} : Set G) = (S : Subgroup G) := by
  obtain ⟨hC', hC, hP', hP, hidx⟩ := h.struct
  obtain ⟨hsS, hsR⟩ := mem_Nsub.mp hsN
  have haS : a ∈ (S : Subgroup G) := h.hRS c.ha
  have hbS : b ∈ (S : Subgroup G) := h.hRS c.hb
  set T := Subgroup.closure ({a, b, s, t'} : Set G) with hT
  have haT : a ∈ T := Subgroup.subset_closure (by simp)
  have hbT : b ∈ T := Subgroup.subset_closure (by simp)
  have ht'T : t' ∈ T := Subgroup.subset_closure (by simp)
  have hsT : s ∈ T := Subgroup.subset_closure (by simp)
  have hRT : R ≤ T := by
    intro r hr
    rcases c.cover r hr with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact T.zpow_mem haT i
    · exact T.mul_mem hbT (T.zpow_mem haT i)
  have hR'T : R' ≤ T := by
    intro x hx
    have hx' : x ∈ conjSub t' R := by rw [h.ht'R]; exact hx
    have h1 := hRT (mem_conjSub_iff.mp hx')
    have e : x = t' * (t'⁻¹ * x * t') * t'⁻¹ := by group
    rw [e]
    exact T.mul_mem (T.mul_mem ht'T h1) (T.inv_mem ht'T)
  have hRRT : R ⊔ R' ≤ T := sup_le hRT hR'T
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · exact haS
    · exact hbS
    · exact hsS
    · exact h.ht'S
  · intro x hx
    have hclN : ∀ y ∈ Nsub S R, y ∈ T := by
      intro y hy
      by_cases hyR : y ∈ R ⊔ R'
      · exact hRRT hyR
      · have hs1 : s⁻¹ ∉ R ⊔ R' := fun h1 => hsn (by simpa using (R ⊔ R').inv_mem h1)
        have hmem : s⁻¹ * y ∈ R ⊔ R' :=
          (mul_mem_iff_of_relIndex_two hidx ((Nsub S R).inv_mem hsN) hy).mpr
            (iff_of_false hs1 hyR)
        have e : y = s * (s⁻¹ * y) := by group
        rw [e]
        exact T.mul_mem hsT (hRRT hmem)
    rcases h.S_cover hx with hxN | htxN
    · exact hclN x hxN
    · have e : x = t'⁻¹ * (t' * x) := by group
      rw [e]
      exact T.mul_mem (T.inv_mem ht'T) (hclN _ htxN)

end T7QEng

end CFSG.ClassicalInvolution.Asc77
