module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Stage
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Sigma
public import CFSG.LocalAnalysis.EvenSporadicStandard.J1.Fusion

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

theorem pgroup_V : IsPGroup 2 H.V :=
  IsPGroup.of_card (n := 4) (by rw [H.card_V]; norm_num)

theorem le_V_of_pgroup_B {P : Subgroup G} (hP : IsPGroup 2 P) (hPB : P ≤ H.B) (hVP : H.V ≤ P) :
    P ≤ H.V := by
  have hdvd : Nat.card P ∣ 336 := H.card_B ▸ Subgroup.card_dvd_of_le hPB
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
  have hn4 : n ≤ 4 := by
    by_contra hcon
    have h32 : 2 ^ 5 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h32.trans (hn ▸ hdvd)
    norm_num at this
  have hle : Nat.card P ≤ 16 := by
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
      _ = 16 := by norm_num
  have := Subgroup.eq_of_le_of_card_ge hVP (by rw [H.card_V]; exact hle)
  rw [← this]


theorem relIndex_E_V : H.E.relIndex H.V = 2 := by
  have := Subgroup.relIndex_mul_card (H := H.E) (K := H.V)
  rw [inf_eq_left.2 H.E_le_V, H.card_E, H.card_V] at this
  omega

theorem exists_tau (hV : 2 ∣ H.V.index) :
    ∃ (T : Sylow 2 G) (τ : G), H.V ≤ T ∧ τ ∈ (T : Subgroup G) ∧
      τ ∈ normalizer (H.V : Set G) ∧ τ ∉ H.V ∧ τ * τ ∈ H.V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hVT⟩ := H.pgroup_V.exists_le_sylow
  have hne : H.V ≠ (T : Subgroup G) := fun heq => T.not_dvd_index (heq ▸ hV)
  obtain ⟨τ₀, hτ₀T, hτ₀N, hτ₀V⟩ :
      ∃ τ ∈ (T : Subgroup G), τ ∈ normalizer (H.V : Set G) ∧ τ ∉ H.V := by
    by_contra hcon
    push Not at hcon
    exact hne (eq_of_inf_normalizer_le T.isPGroup' hVT hcon)
  have hex : ∃ j : ℕ, τ₀ ^ (2 ^ j) ∈ H.V := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.1 T.isPGroup' ⟨τ₀, hτ₀T⟩
    refine ⟨a, ?_⟩
    have : τ₀ ^ (2 ^ a) = 1 := by
      have h1 : orderOf τ₀ = 2 ^ a :=
        (Subgroup.orderOf_coe (⟨τ₀, hτ₀T⟩ : (T : Subgroup G))).trans ha
      rw [← h1]
      exact pow_orderOf_eq_one τ₀
    rw [this]
    exact one_mem _
  classical
  set j₀ := Nat.find hex with hj₀
  have hj₀spec : τ₀ ^ (2 ^ j₀) ∈ H.V := Nat.find_spec hex
  have hj₀pos : j₀ ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hj₀spec
    exact hτ₀V hj₀spec
  obtain ⟨j, hj⟩ : ∃ j, j₀ = j + 1 := ⟨j₀ - 1, by omega⟩
  have hjnot : τ₀ ^ (2 ^ j) ∉ H.V := Nat.find_min hex (by omega)
  refine ⟨T, τ₀ ^ (2 ^ j), hVT, pow_mem hτ₀T _, pow_mem hτ₀N _, hjnot, ?_⟩
  rw [← pow_two, ← pow_mul, ← pow_succ]
  rw [hj] at hj₀spec
  exact hj₀spec


theorem exists_fixed {τ : G} (hτN : τ ∈ normalizer (H.V : Set G)) (hτ2 : τ * τ ∈ H.V) :
    ∃ e ∈ H.E, e ≠ 1 ∧ τ * e * τ⁻¹ = e := by
  set α : MulAut ↥H.V := H.V.normalizerMonoidHom ⟨τ, hτN⟩ with hα
  have hαapp : ∀ v : H.V, ((α v : H.V) : G) = τ * v * τ⁻¹ := fun v => rfl
  have hcomm : ∀ a b : H.V, a * b = b * a := fun a b => Subtype.ext (H.V_comm a.2 b.2)
  have hsq : ∀ a : H.V, a * a = 1 := fun a => Subtype.ext (H.V_sq a.2)
  have hinv : ∀ a : H.V, a⁻¹ = a := fun a => inv_eq_of_mul_eq_one_right (hsq a)
  let _ : CommGroup ↥H.V := { (inferInstance : Group ↥H.V) with mul_comm := hcomm }
  have hα2 : ∀ v : H.V, α (α v) = v := by
    intro v
    apply Subtype.ext
    rw [hαapp, hαapp]
    have := H.V_comm hτ2 v.2
    calc τ * (τ * v * τ⁻¹) * τ⁻¹ = (τ * τ) * v * (τ * τ)⁻¹ := by group
      _ = v := by rw [this]; group
  let δ : H.V →* H.V := (MonoidHom.id H.V)⁻¹ * α.toMonoidHom
  have hδ : ∀ v : H.V, δ v = v⁻¹ * α v := fun v => rfl
  have hker : ∀ v : H.V, v ∈ δ.ker ↔ α v = v := by
    intro v
    rw [MonoidHom.mem_ker, hδ, inv_mul_eq_one]
    exact eq_comm
  have hrange : δ.range ≤ δ.ker := by
    rintro _ ⟨v, rfl⟩
    rw [hker, hδ, map_mul, map_inv, hα2, hinv (α v), hinv v]
    exact hcomm _ _
  have hcard := Subgroup.card_ker_mul_card_range δ
  have hle : Nat.card δ.range ≤ Nat.card δ.ker := Subgroup.card_le_of_le hrange
  have hVcard : Nat.card H.V = 16 := H.card_V
  have hk4 : 4 ≤ Nat.card δ.ker := by
    by_contra hcon
    push Not at hcon
    have : Nat.card δ.ker * Nat.card δ.range ≤ 3 * 3 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega
  set C : Subgroup G := δ.ker.map H.V.subtype with hC
  have hCcard : Nat.card C = Nat.card δ.ker :=
    Subgroup.card_map_of_injective H.V.subtype_injective
  have hCV : C ≤ H.V := by
    rintro _ ⟨k, _, rfl⟩
    exact k.2
  have hCfix : ∀ c ∈ C, τ * c * τ⁻¹ = c := by
    rintro _ ⟨k, hk, rfl⟩
    have := congrArg (fun a : H.V => (a : G)) ((hker k).1 hk)
    simpa [hαapp] using this
  have hrel := Subgroup.relIndex_mul_card (H := H.E) (K := C)
  have hrel2 : H.E.relIndex C ≤ 2 := by
    have := Subgroup.relIndex_le_of_le_right (H := H.E) hCV (by rw [H.relIndex_E_V]; norm_num)
    rwa [H.relIndex_E_V] at this
  have hEC : 2 ≤ Nat.card (H.E ⊓ C : Subgroup G) := by
    by_contra hcon
    push Not at hcon
    have : H.E.relIndex C * Nat.card (H.E ⊓ C : Subgroup G) ≤ 2 * 1 :=
      Nat.mul_le_mul hrel2 (by omega)
    omega
  have hne : (H.E ⊓ C : Subgroup G) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot]
    omega
  obtain ⟨⟨e, he⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  exact ⟨e, he.1, fun h1 => hne1 (Subtype.ext h1), hCfix e he.2⟩


theorem exists_stage_one (hV : 2 ∣ H.V.index) : Stage H H.V H.E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, τ, hVT, hτT, hτN, hτV, hτ2⟩ := H.exists_tau hV
  obtain ⟨e, heE, he1, hτe⟩ := H.exists_fixed hτN hτ2
  obtain ⟨σ, hσNL, hσ7⟩ := H.exists_sigma
  obtain ⟨-, htrans⟩ := H.sigma_orbit hσNL hσ7
  have hσL : σ ∈ H.L := (H.mem_NL_iff.1 hσNL).1
  have hσz : ∀ i : ℕ, σ ^ i * H.z * (σ ^ i)⁻¹ = H.z := by
    intro i
    have := H.comm_z (pow_mem hσL i)
    calc σ ^ i * H.z * (σ ^ i)⁻¹ = H.z * σ ^ i * (σ ^ i)⁻¹ := by rw [this]
      _ = H.z := by group
  have henot : ¬ IsConj H.z e := by
    intro hconj
    set P : Subgroup G := centralizer ({e} : Set G) ⊓ (T : Subgroup G) with hP
    have hPp : IsPGroup 2 P := T.isPGroup'.to_inf_right
    have hVP : H.V ≤ P := fun v hv => ⟨mem_centralizer_singleton_iff.2
      (H.V_comm hv (H.E_le_V heE)), hVT hv⟩
    have hτP : τ ∈ P := ⟨mem_centralizer_singleton_iff.2 (by
      calc τ * e = τ * e * τ⁻¹ * τ := by group
        _ = e * τ := by rw [hτe]), hτT⟩
    have hlt : H.V < P := lt_of_le_of_ne hVP (fun h => hτV (h ▸ hτP))
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := (H.star_conj hconj hPp inf_le_left).1
    rw [H.card_V] at h1
    omega
  have hnoconj : ∀ e' ∈ H.E, ¬ IsConj H.z e' := by
    intro e' he' hc
    by_cases h1 : e' = 1
    · subst h1
      exact H.z_ne_one (isConj_one_right.1 hc.symm)
    · obtain ⟨i, hi⟩ := htrans e heE e' he' he1 h1
      have hce : IsConj e e' := isConj_iff.2 ⟨σ ^ i, hi⟩
      exact henot (hc.trans hce.symm)
  have hwV : τ * H.z * τ⁻¹ ∈ H.V := (mem_normalizer_iff.1 hτN H.z).1 H.z_mem_V
  have hwz : τ * H.z * τ⁻¹ ≠ H.z := by
    intro hw
    have hτB : τ ∈ H.B := H.mem_B_def.2 ⟨hτN, mem_centralizer_singleton_iff.2 (by
      calc τ * H.z = τ * H.z * τ⁻¹ * τ := by group
        _ = H.z * τ := by rw [hw])⟩
    set P : Subgroup G := H.B ⊓ (T : Subgroup G) with hP
    have hPp : IsPGroup 2 P := T.isPGroup'.to_inf_right
    have hVP : H.V ≤ P := le_inf H.V_le_B hVT
    exact hτV (H.le_V_of_pgroup_B hPp inf_le_left hVP ⟨hτB, hτT⟩)
  have hwconj : IsConj H.z (τ * H.z * τ⁻¹) := isConj_iff.2 ⟨τ, rfl⟩
  obtain ⟨e₁, he₁, hw⟩ : ∃ e₁ ∈ H.E, τ * H.z * τ⁻¹ = e₁ * H.z := by
    rcases H.mem_V_iff'.1 hwV with h | ⟨e₁, he₁, hw⟩
    · exact absurd hwconj (hnoconj _ h)
    · exact ⟨e₁, he₁, hw⟩
  have he₁1 : e₁ ≠ 1 := fun h1 => hwz (by rw [hw, h1, one_mul])
  have hzE : ∀ e'' ∈ H.E, IsConj H.z (e'' * H.z) := by
    intro e'' he''
    by_cases h1 : e'' = 1
    · subst h1
      rw [one_mul]
    · obtain ⟨i, hi⟩ := htrans e₁ he₁ e'' he'' he₁1 h1
      have : σ ^ i * (e₁ * H.z) * (σ ^ i)⁻¹ = e'' * H.z := by
        calc σ ^ i * (e₁ * H.z) * (σ ^ i)⁻¹
            = (σ ^ i * e₁ * (σ ^ i)⁻¹) * (σ ^ i * H.z * (σ ^ i)⁻¹) := by group
          _ = e'' * H.z := by rw [hi, hσz]
      have hc2 : IsConj (e₁ * H.z) (e'' * H.z) := isConj_iff.2 ⟨σ ^ i, this⟩
      rw [← hw] at hc2
      exact hwconj.trans hc2
  refine ⟨H.pgroup_V, H.E_le_V, H.z_mem_V, H.z_not_mem_E, fun s hs => H.mem_V_iff.1 hs, le_rfl,
    fun s hs hsE => ?_, hnoconj, fun b hb => (H.mem_B_def.1 hb).1⟩
  rcases H.mem_V_iff'.1 hs with h | ⟨e'', he'', rfl⟩
  · exact absurd h hsE
  · exact hzE e'' he''

end Setting

end CFSG.EvenSporadicStandard.J1Std
