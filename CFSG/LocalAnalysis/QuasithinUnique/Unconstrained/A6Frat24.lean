module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsModel4
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Frat24Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Datum

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin A6Facts

section Frat24

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs}

theorem Notation25.x_conj_S {s : G} (hs' : s ∈ N.S) : N.x * s * N.x⁻¹ ∈ N.S :=
  (Subgroup.mem_normalizer_iff.mp N.x_mem.2 s).mp hs'

theorem Notation25.x_conj_S' {s : G} (hs' : s ∈ N.S) : N.x⁻¹ * s * N.x ∈ N.S := by
  have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ N.x_mem.2) s).mp hs'
  simpa using this

theorem A6Datum.mem_S_of_Φ_mem_P0 (D : A6Datum N) (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h254 : Facts254 N) (hsimple : IsSimpleGroup ↥N.K) {c : G} (hcH : c ∈ N.H)
    (hP : D.Φ c ∈ P0) : c ∈ N.S := by
  obtain ⟨s, hs, hsc⟩ := D.S_surj _ hP
  have hsH := N.S_le_H hs
  have h1 : D.Φ (s⁻¹ * c) = 1 := by
    rw [D.mul _ (N.H.inv_mem hsH) _ hcH, D.Φ_inv hsH, hsc, inv_mul_cancel]
  have h2 := (D.ker _ (N.H.mul_mem (N.H.inv_mem hsH) hcH)).mp h1
  have hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have h3 : s⁻¹ * c ∈ N.S :=
    N.mem_S_of_centralizes hKH h254 hZ (N.H.mul_mem (N.H.inv_mem hsH) hcH) h2
  have : c = s * (s⁻¹ * c) := by group
  rw [this]
  exact N.S.mul_mem hs h3

theorem A6Datum.Φ_z (D : A6Datum N) (hK0 : N.K0 = N.K) (h254 : Facts254 N)
    (hzS : N.z ∈ centerOf N.S) : D.Φ N.z = zb := by
  have hzS' : N.z ∈ N.S := hzS.1
  have hzH : N.z ∈ N.H := N.S_le_H hzS'
  have hz1 : D.Φ N.z ≠ 1 := fun h1 => h254.z_not_mem (D.mem_SC_of_Φ_eq_one hK0 hzS' h1)
  have hcent : ∀ p ∈ P0, D.Φ N.z * p = p * D.Φ N.z := by
    intro p hp
    obtain ⟨s, hs, rfl⟩ := D.S_surj p hp
    have hsz : N.z * s = s * N.z := (Subgroup.mem_centralizer_iff.mp hzS.2 s hs).symm
    rw [← D.mul _ hzH _ (N.S_le_H hs), ← D.mul _ (N.S_le_H hs) _ hzH, hsz]
  rcases center_P0 (D.S_mem _ hzS') hcent with h | h
  · exact absurd h hz1
  · exact h

theorem A6Datum.Φ_zK {t zK : G} (D : A6Datum N) (hK0 : N.K0 = N.K) (hf : Facts2511 N t zK) :
    D.Φ zK = D.Φ N.z := by
  have hzKH : zK ∈ N.H := N.K_le_H (hK0 ▸ hf.zK_mem)
  have hzH : N.z ∈ N.H := N.S_le_H (N.tuple.center_le N.tuple.z_mem)
  have h1 := D.Φ_eq_one_of_mem_SC hK0 hf.zK_proj
  rw [D.mul _ (N.H.inv_mem hzKH) _ hzH, D.Φ_inv hzKH] at h1
  exact inv_mul_eq_one.mp h1

theorem A6Datum.zK_ne_one {zK : G} (D : A6Datum N) (hΦzK : D.Φ zK = zb) : zK ≠ 1 := by
  intro h
  rw [h, D.Φ_one] at hΦzK
  exact zb_ne_one hΦzK.symm

theorem A6Datum.pow_four {t zK : G} (D : A6Datum N) (hK0 : N.K0 = N.K)
    (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (h254 : Facts254 N)
    (hsimple : IsSimpleGroup ↥N.K) (hf : Facts2511 N t zK) (hΦzK : D.Φ zK = zb)
    (hSC2 : ∀ a ∈ N.SC, a * a = 1) {s : G} (hs : s ∈ N.S) :
    (s ^ 4 = 1 ∧ D.Φ s ^ 4 = 1) ∨ (s ^ 4 = zK ∧ D.Φ s ^ 4 = zb) := by
  have hsH := N.S_le_H hs
  have hfS : s * s ∈ N.S := N.S.mul_mem hs hs
  have hΦf : D.Φ (s * s) = D.Φ s * D.Φ s := D.mul s hsH s hsH
  obtain ⟨hfP, hfpsl⟩ := sq_mem_D (D.S_mem s hs)
  obtain ⟨y, hySK, hyΦ⟩ := D.exists_mem_SK hKH h254 hsimple hfP hfpsl
  have hyS : y ∈ N.S := N.SK_le_S hySK
  have hyK : y ∈ N.K := hySK.2
  have hc : y⁻¹ * (s * s) ∈ N.SC := D.inv_mul_mem_SC hK0 hyS hfS (by rw [hyΦ, hΦf])
  have hcomm : y * (y⁻¹ * (s * s)) = (y⁻¹ * (s * s)) * y :=
    Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hc) y (hK0 ▸ hyK)
  have hcc : (y⁻¹ * (s * s)) * (y⁻¹ * (s * s)) = 1 := hSC2 _ hc
  have hs4 : s ^ 4 = y * y := by
    have e1 : s ^ 4 = (s * s) * (s * s) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    have e2 : s * s = y * (y⁻¹ * (s * s)) := by group
    set c := y⁻¹ * (s * s) with hcdef
    calc s ^ 4 = (s * s) * (s * s) := e1
      _ = (y * c) * (y * c) := by rw [← e2]
      _ = y * (c * y) * c := by group
      _ = y * (y * c) * c := by rw [← hcomm]
      _ = y * y * (c * c) := by group
      _ = y * y := by rw [hcc, mul_one]
  have hyy : D.Φ (y * y) = D.Φ s ^ 4 := by
    rw [D.mul y (N.K_le_H hyK) y (N.K_le_H hyK), hyΦ, show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  have hyyK : y * y ∈ N.K := N.K.mul_mem hyK hyK
  rcases pow4_of_mem (D.S_mem s hs) with h1 | h1
  · left
    refine ⟨?_, h1⟩
    rw [hs4]
    exact D.inj_K hsimple hyyK N.K.one_mem (by rw [hyy, h1, D.Φ_one])
  · right
    refine ⟨?_, h1⟩
    rw [hs4]
    exact D.inj_K hsimple hyyK (hK0 ▸ hf.zK_mem) (by rw [hyy, h1, hΦzK])

theorem A6Datum.x_zK {t zK : G} (D : A6Datum N) (hK0 : N.K0 = N.K)
    (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (h254 : Facts254 N)
    (hsimple : IsSimpleGroup ↥N.K) (hf : Facts2511 N t zK) (hΦzK : D.Φ zK = zb)
    (hSC2 : ∀ a ∈ N.SC, a * a = 1) : N.x⁻¹ * zK * N.x = zK := by
  obtain ⟨p, hpP, hp4⟩ := exists_pow4
  obtain ⟨s₀, hs₀, hΦs₀⟩ := D.S_surj p hpP
  have hs₀4 : s₀ ^ 4 = zK := by
    rcases D.pow_four hK0 hKH h254 hsimple hf hΦzK hSC2 hs₀ with ⟨-, h⟩ | ⟨h, -⟩
    · rw [hΦs₀, hp4] at h
      exact absurd h zb_ne_one
    · exact h
  have hxs : N.x⁻¹ * s₀ * N.x ∈ N.S := N.x_conj_S' hs₀
  have e : N.x⁻¹ * zK * N.x = (N.x⁻¹ * s₀ * N.x) ^ 4 := by
    rw [← hs₀4]
    have := conj_pow (a := N.x⁻¹) (b := s₀) (i := 4)
    simpa using this.symm
  rcases D.pow_four hK0 hKH h254 hsimple hf hΦzK hSC2 hxs with ⟨h, -⟩ | ⟨h, -⟩
  · exfalso
    rw [h] at e
    apply D.zK_ne_one hΦzK
    have : N.x⁻¹ * zK * N.x = 1 := e
    calc zK = N.x * (N.x⁻¹ * zK * N.x) * N.x⁻¹ := by group
      _ = 1 := by rw [this]; group
  · rw [e]
    exact h

theorem A6Datum.four_subgroup_data {t zK : G} (D : A6Datum N) (hK0 : N.K0 = N.K)
    (hsimple : IsSimpleGroup ↥N.K) (hf : Facts2511 N t zK) (hΦzK : D.Φ zK = zb) {E : Subgroup G}
    (hEK : E ≤ N.SK) (hE : IsFourSubgroup E) :
    zK ∈ E ∧ ∃ e ∈ E, e ≠ 1 ∧ e ≠ zK ∧ IsRefl (D.Φ e) ∧ e * e = 1 ∧
      ∀ x ∈ E, x = 1 ∨ x = zK ∨ x = e ∨ x = e * zK := by
  have hE4 : Nat.card E = 4 := hE.2
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by simpa [sq] using hE.1.2 x hx
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => isElemAbelian_mul_comm hE.1 hx hy
  have hKmem : ∀ x ∈ E, x ∈ N.K := fun x hx => (hEK hx).2
  have hΦP : ∀ x ∈ E, D.Φ x ∈ P0 := fun x hx => D.S_mem x (N.SK_le_S (hEK hx))
  have hΦpsl : ∀ x ∈ E, D.Φ x ∈ A6Models.psl29 := fun x hx => D.K_mem x (hKmem x hx)
  have hΦne : ∀ x ∈ E, x ≠ 1 → D.Φ x ≠ 1 := by
    intro x hx hx1 h
    apply hx1
    exact D.inj_K hsimple (hKmem x hx) N.K.one_mem (by rw [h, D.Φ_one])
  have hΦinj : ∀ x ∈ E, ∀ y ∈ E, D.Φ x = D.Φ y → x = y := fun x hx y hy h =>
    D.inj_K hsimple (hKmem x hx) (hKmem y hy) h
  have hΦsq : ∀ x ∈ E, D.Φ x * D.Φ x = 1 := by
    intro x hx
    rw [← D.mul x (N.K_le_H (hKmem x hx)) x (N.K_le_H (hKmem x hx)), hE2 x hx, D.Φ_one]
  obtain ⟨e₁, he₁E, he₁1, -⟩ := exists_mem_ne_two hE4 1 1
  obtain ⟨e₂, he₂E, he₂1, he₂e₁⟩ := exists_mem_ne_two hE4 1 e₁
  have hzKE : zK ∈ E := by
    have hcomm : D.Φ e₁ * D.Φ e₂ = D.Φ e₂ * D.Φ e₁ := by
      rw [← D.mul e₁ (N.K_le_H (hKmem _ he₁E)) e₂ (N.K_le_H (hKmem _ he₂E)),
        ← D.mul e₂ (N.K_le_H (hKmem _ he₂E)) e₁ (N.K_le_H (hKmem _ he₁E)), hEc e₁ he₁E e₂ he₂E]
    have hkl := d_klein_zb_mem (hΦP e₁ he₁E) (hΦpsl e₁ he₁E) (hΦP e₂ he₂E) (hΦpsl e₂ he₂E)
      (hΦne e₁ he₁E he₁1) (hΦsq e₁ he₁E) (hΦne e₂ he₂E he₂1)
      (fun h => he₂e₁ (hΦinj _ he₂E _ he₁E h)) (hΦsq e₂ he₂E) hcomm
    have hzKK : zK ∈ N.K := hK0 ▸ hf.zK_mem
    rcases hkl with h | h | h
    · have : e₁ = zK := D.inj_K hsimple (hKmem _ he₁E) hzKK (by rw [h, hΦzK])
      rw [← this]; exact he₁E
    · have : e₂ = zK := D.inj_K hsimple (hKmem _ he₂E) hzKK (by rw [h, hΦzK])
      rw [← this]; exact he₂E
    · have : e₁ * e₂ = zK := D.inj_K hsimple (hKmem _ (E.mul_mem he₁E he₂E)) hzKK (by
        rw [D.mul e₁ (N.K_le_H (hKmem _ he₁E)) e₂ (N.K_le_H (hKmem _ he₂E)), h, hΦzK])
      rw [← this]; exact E.mul_mem he₁E he₂E
  obtain ⟨e, heE, he1, hezK⟩ := exists_mem_ne_two hE4 1 zK
  have hzK1 : zK ≠ 1 := D.zK_ne_one hΦzK
  refine ⟨hzKE, e, heE, he1, hezK, ⟨hΦP e heE, hΦpsl e heE, hΦne e heE he1, ?_, hΦsq e heE⟩,
    hE2 e heE, ?_⟩
  · intro h
    exact hezK (hΦinj _ heE _ hzKE (by rw [h, hΦzK]))
  · intro x hx
    have := four_subgroup_elems hE4 hzKE heE hzK1 he1 (Ne.symm hezK) (hE2 zK hzKE) (hE2 e heE) x hx
    rcases this with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (by rw [h, hEc zK hzKE e heE])))

@[expose] def Notation25.CS (N : Notation25 hs) (E : Subgroup G) : Subgroup G :=
  N.S ⊓ Subgroup.centralizer (E : Set G)

theorem Notation25.mem_CS_iff {E : Subgroup G} {b : G} :
    b ∈ N.CS E ↔ b ∈ N.S ∧ ∀ e ∈ E, e * b = b * e := by
  unfold Notation25.CS
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  rfl

theorem A6Datum.centralizer_le_S {t zK : G} (D : A6Datum N) (hK0 : N.K0 = N.K)
    (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (h254 : Facts254 N)
    (hsimple : IsSimpleGroup ↥N.K) (hf : Facts2511 N t zK) (hΦzK : D.Φ zK = zb)
    {E : Subgroup G} (hEK : E ≤ N.SK) (hE : IsFourSubgroup E) {c : G} (hcH : c ∈ N.H)
    (hcE : ∀ e ∈ E, e * c = c * e) : c ∈ N.S := by
  obtain ⟨hzKE, e, heE, he1, hezK, hrefl, he2, hEel⟩ :=
    D.four_subgroup_data hK0 hsimple hf hΦzK hEK hE
  obtain ⟨β, hβ, hβd⟩ := exists_E4_not_psl
  have heH : e ∈ N.H := N.K_le_H (hEK heE).2
  have hzKH : zK ∈ N.H := N.K_le_H (hEK hzKE).2
  have hqr : D.Φ c * D.Φ e = D.Φ e * D.Φ c := by
    rw [← D.mul c hcH e heH, ← D.mul e heH c hcH, hcE e heE]
  have hqz : D.Φ c * zb = zb * D.Φ c := by
    rw [← hΦzK, ← D.mul c hcH zK hzKH, ← D.mul zK hzKH c hcH, hcE zK hzKE]
  have h1 := klein_cent_aut hrefl hβ hβd (D.mem c hcH) hqr hqz
  exact D.mem_S_of_Φ_mem_P0 hKH h254 hsimple hcH h1.1

theorem A6Datum.conj_mem_CS {t zK : G} (D : A6Datum N) (hK0 : N.K0 = N.K)
    (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (h254 : Facts254 N)
    (hsimple : IsSimpleGroup ↥N.K) (hf : Facts2511 N t zK) (hΦzK : D.Φ zK = zb)
    {E : Subgroup G} (hEK : E ≤ N.SK) (hE : IsFourSubgroup E) {c q : G} (hcH : c ∈ N.H)
    (hcN : c ∈ Subgroup.normalizer (E : Set G)) (hq : q ∈ N.CS E) : c * q * c⁻¹ ∈ N.CS E := by
  rw [Notation25.mem_CS_iff] at hq ⊢
  obtain ⟨hqS, hqE⟩ := hq
  have hcqH : c * q * c⁻¹ ∈ N.H := N.H.mul_mem (N.H.mul_mem hcH (N.S_le_H hqS)) (N.H.inv_mem hcH)
  have hcomm : ∀ e ∈ E, e * (c * q * c⁻¹) = (c * q * c⁻¹) * e := by
    intro e he
    have he' : c⁻¹ * e * c ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) e).mp he
      simpa using this
    have h1 := hqE _ he'
    calc e * (c * q * c⁻¹) = c * ((c⁻¹ * e * c) * q) * c⁻¹ := by group
      _ = c * (q * (c⁻¹ * e * c)) * c⁻¹ := by rw [h1]
      _ = (c * q * c⁻¹) * e := by group
  exact ⟨D.centralizer_le_S hK0 hKH h254 hsimple hf hΦzK hEK hE hcqH (fun e he => hcomm e he),
    hcomm⟩

theorem A6Datum.sylow_CS {t zK : G} (D : A6Datum N) (h : Lv2523 N t zK) (hK0 : N.K0 = N.K)
    (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) (hΦzK : D.Φ zK = zb)
    {E : Subgroup G} (hEK : E ≤ N.SK) (hE : IsFourSubgroup E)
    (hstar : IsUStarPair M N.H (N.S ⊓ Subgroup.normalizer (E : Set G))
      (N.H ⊓ Subgroup.normalizer (E : Set G))) :
    IsSylowTwoOf (N.S ⊓ Subgroup.normalizer (E : Set G))
      (Subgroup.normalizer ((N.CS E : Subgroup G) : Set G)) := by
  have hf := h.facts2511
  have h254 := h.facts254
  have hsimple := h.facts258.simple
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hzS : N.z ∈ centerOf N.S :=
    ⟨N.tuple.center_le hzT,
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr N.S_le_T) hzT.2⟩
  have hQ2 : IsPGroup 2 ↥(N.CS E) := N.tuple.sylow.isPGroup.to_le inf_le_left
  have hzQ : N.z ∈ N.CS E := by
    rw [Notation25.mem_CS_iff]
    exact ⟨hzS.1, fun e he => Subgroup.mem_centralizer_iff.mp hzS.2 e (N.SK_le_S (hEK he))⟩
  have hQHU : N.CS E ≤ N.H ⊓ Subgroup.normalizer (E : Set G) := by
    intro q hq
    rw [Notation25.mem_CS_iff] at hq
    refine ⟨N.S_le_H hq.1, Subgroup.mem_normalizer_iff.mpr fun x => ?_⟩
    constructor
    · intro hx
      have hxq := hq.2 x hx
      have e : q * x * q⁻¹ = x := by
        calc q * x * q⁻¹ = (q * x) * q⁻¹ := rfl
          _ = (x * q) * q⁻¹ := by rw [← hxq]
          _ = x := by group
      show q * x * q⁻¹ ∈ E
      rw [e]
      exact hx
    · intro hx
      have hx' : q * x * q⁻¹ ∈ E := hx
      have hy := hq.2 _ hx'
      have h1 : q * x = q * (q * x * q⁻¹) := by
        calc q * x = (q * x * q⁻¹) * q := by group
          _ = q * (q * x * q⁻¹) := hy
      have h2 : x = q * x * q⁻¹ := mul_left_cancel h1
      show x ∈ E
      rw [h2]
      exact hx'
  have hHUQ : N.H ⊓ Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer ((N.CS E : Subgroup G) : Set G) := by
    intro c hc
    refine Subgroup.mem_normalizer_iff.mpr fun q => ⟨fun hq => ?_, fun hq => ?_⟩
    · exact D.conj_mem_CS hK0 hKH h254 hsimple hf hΦzK hEK hE hc.1 hc.2 hq
    · have := D.conj_mem_CS hK0 hKH h254 hsimple hf hΦzK hEK hE (N.H.inv_mem hc.1)
        (Subgroup.inv_mem _ hc.2) hq
      simpa [mul_assoc] using this
  exact (((h.concl2512 hKH).1 _ _ hstar inf_le_left).2 (N.CS E) hQ2 hzQ hQHU hHUQ).2

theorem A6Datum.exists_conj_zK {t zK : G} (D : A6Datum N) (hK0 : N.K0 = N.K)
    (hsimple : IsSimpleGroup ↥N.K) (hf : Facts2511 N t zK) (hΦzK : D.Φ zK = zb) {e : G}
    (heSK : e ∈ N.SK) (he1 : e ≠ 1) (he2 : e * e = 1) : ∃ k ∈ N.K, k * zK * k⁻¹ = e := by
  have heK : e ∈ N.K := heSK.2
  have heH : e ∈ N.H := N.K_le_H heK
  have hΦne : D.Φ e ≠ 1 := by
    intro h
    apply he1
    exact D.inj_K hsimple heK N.K.one_mem (by rw [h, D.Φ_one])
  have hΦsq : D.Φ e * D.Φ e = 1 := by
    rw [← D.mul e heH e heH, he2, D.Φ_one]
  obtain ⟨g, hg, hgz⟩ := conj_zb (D.S_mem e (N.SK_le_S heSK)) (D.K_mem e heK) hΦne hΦsq
  obtain ⟨k, hk, hkΦ⟩ := D.K_surj g hg
  have hkH : k ∈ N.H := N.K_le_H hk
  have hzKK : zK ∈ N.K := hK0 ▸ hf.zK_mem
  have hzKH : zK ∈ N.H := N.K_le_H hzKK
  refine ⟨k, hk, ?_⟩
  have h1 : k * zK = e * k := by
    apply D.inj_K hsimple (N.K.mul_mem hk hzKK) (N.K.mul_mem heK hk)
    rw [D.mul k hkH zK hzKH, D.mul e heH k hkH, hkΦ, hΦzK, hgz]
  calc k * zK * k⁻¹ = (e * k) * k⁻¹ := by rw [h1]
    _ = e := by group

end Frat24
