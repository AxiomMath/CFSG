module

public import CFSG.CGT.A8S.L2GModel
public import CFSG.CGT.T75JM.L2GAdjust

public section

namespace CFSG.CGT.A8S.L2

open CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.CGT.T75JM

variable {G H : Type*} [Group G] [Group H]

theorem inv_mul_mem_of_card_eq_two_mul {K L : Subgroup G} (hKL : K ≤ L)
    (hL : Nat.card L = 2 * Nat.card K) (hK : Nat.card K ≠ 0) {u v : G} (hu : u ∈ L) (hv : v ∈ L)
    (hu' : u ∉ K) (hv' : v ∉ K) : u⁻¹ * v ∈ K := by
  have hidx : (K.subgroupOf L).index = 2 := by
    have h1 := (K.subgroupOf L).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv, hL, mul_comm 2] at h1
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hK) h1
  have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨u⁻¹, L.inv_mem hu⟩)
    (b := ⟨v, hv⟩)).2 (by
      simp only [Subgroup.mem_subgroupOf]
      exact ⟨fun h => absurd (by simpa using K.inv_mem h) hu', fun h => absurd h hv'⟩)
  rwa [Subgroup.mem_subgroupOf] at h

theorem inv_mul_mem_normIn {T T₁ : Subgroup G} (h : TCtx T T₁) (h8 : Nat.card T₁ = 8)
    {u v : G} (hu : u ∈ T₁) (hv : v ∈ T₁) (hu' : u ∉ Subgroup.normalizer (T : Set G))
    (hv' : v ∉ Subgroup.normalizer (T : Set G)) : u⁻¹ * v ∈ normIn T₁ T :=
  inv_mul_mem_of_card_eq_two_mul (normIn_le T₁ T) (by rw [h8, h.norm2]) (by rw [h.norm2]; norm_num)
    hu hv (fun h' => hu' (mem_normIn.1 h').2) (fun h' => hv' (mem_normIn.1 h').2)

theorem comm_commutator {T₁ : Subgroup G} (hT₁ : IsElemAbelian 2 T₁) {t₁ a : G} (ht₁ : t₁ ∈ T₁)
    (ha : a ∈ Subgroup.normalizer (T₁ : Set G)) (ha2 : a * a = 1) :
    a * (t₁ * a * t₁⁻¹ * a⁻¹) = (t₁ * a * t₁⁻¹ * a⁻¹) * a := by
  have hu : a * t₁ * a⁻¹ ∈ T₁ := (Subgroup.mem_normalizer_iff.1 ha t₁).1 ht₁
  have hc := elemAbelian_mul_comm hT₁ hu ht₁
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have ht₁inv : t₁⁻¹ = t₁ := elemAbelian_inv hT₁ ht₁
  rw [hainv] at hc
  rw [hainv, ht₁inv]
  calc a * (t₁ * a * t₁ * a) = (a * t₁ * a * t₁) * a := by group
    _ = (t₁ * (a * t₁ * a)) * a := by rw [hc]
    _ = t₁ * a * t₁ * a * a := by group

theorem exists_swapperA8 {T T₁ : Subgroup G} (h : TCtx T T₁) (h8 : Nat.card T₁ = 8)
    (M : T1ModelA8 H) {E : OntoEmb H (Subgroup.normalizer (T : Set G))}
    (hT : ∀ x, x ∈ M.T0 ↔ E.Φ x ∈ T) (hB : ∀ x, x ∈ M.B0 ↔ E.Φ x ∈ T₁) :
    ∃ g : G, conjSubgroup g T = T₁ ∧ conjSubgroup g T₁ = T := by
  classical
  have hB0 : M.B0 = T₁.comap E.Φ := by
    ext x
    rw [hB x]
    rfl
  have hD : ∀ x : H, x ∈ Subgroup.normalizer (M.B0 : Set H) ↔
      E.Φ x ∈ Subgroup.normalizer (T₁ : Set G) := by
    intro x
    rw [hB0]
    exact h.mem_normalizer_comap_iff E x
  have hne : ∀ x : H, x ≠ 1 → E.Φ x ≠ 1 := fun x hx h' =>
    hx (E.inj (h'.trans (map_one _).symm))
  have htT : E.Φ M.tau ∈ T := (hT _).1 M.tau_mem
  have htN₁ : E.Φ M.tau ∉ Subgroup.normalizer (T₁ : Set G) := fun h' => M.tau_not ((hD _).2 h')
  have hb₁T₁ : E.Φ M.beta ∈ T₁ := (hB _).1 M.beta_mem
  have hb₁B : E.Φ M.beta ∈ normIn T₁ T := mem_normIn.2 ⟨hb₁T₁, E.mem _⟩
  have hb₁1 := hne _ M.beta_ne
  have ha₁T : E.Φ (M.tau * M.beta * M.tau⁻¹ * M.beta⁻¹) ∈ T := (hT _).1 M.comm_mem
  have ha₁A : E.Φ (M.tau * M.beta * M.tau⁻¹ * M.beta⁻¹) ∈ normIn T T₁ :=
    mem_normIn.2 ⟨ha₁T, (hD _).1 M.comm_norm⟩
  have ha₁1 := hne _ M.comm_ne
  have hσa : E.Φ (M.d 1) * E.Φ (M.tau * M.beta * M.tau⁻¹ * M.beta⁻¹) =
      E.Φ (M.tau * M.beta * M.tau⁻¹ * M.beta⁻¹) * E.Φ (M.d 1) := by
    rw [← map_mul, ← map_mul, M.sig_comm]
  have ha₁def : E.Φ (M.tau * M.beta * M.tau⁻¹ * M.beta⁻¹) =
      E.Φ M.tau * E.Φ M.beta * (E.Φ M.tau)⁻¹ * (E.Φ M.beta)⁻¹ := by
    simp only [map_mul, map_inv]
  set t := E.Φ M.tau with ht
  set b₁ := E.Φ M.beta with hb₁
  set a₁ := E.Φ (M.tau * M.beta * M.tau⁻¹ * M.beta⁻¹) with ha₁
  obtain ⟨t₁, ht₁T₁, ht₁N⟩ : ∃ t₁ ∈ T₁, t₁ ∉ Subgroup.normalizer (T : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : T₁ ≤ normIn T₁ T := fun x hx => mem_normIn.2 ⟨hx, hcon x hx⟩
    have hfin : Finite (normIn T₁ T) := Nat.finite_of_card_ne_zero (by rw [h.norm2]; norm_num)
    have := Subgroup.card_le_of_le hle
    rw [h8, h.norm2] at this
    omega
  have ha₁N₁ : a₁ ∈ Subgroup.normalizer (T₁ : Set G) := (mem_normIn.1 ha₁A).2
  have ha₁2 : a₁ * a₁ = 1 := elemAbelian_mul_self h.wc.1 ha₁T
  have hcent : ∀ y, a₁ * y = y * a₁ → y ∈ Subgroup.normalizer (T : Set G) := fun y hy =>
    h.wc.centralizer_le_normalizer ha₁T ha₁1 (Subgroup.mem_centralizer_singleton_iff.2 hy.symm)
  have hb₂c := comm_commutator h.elemAbelian₁ ht₁T₁ ha₁N₁ ha₁2
  set b₂ := t₁ * a₁ * t₁⁻¹ * a₁⁻¹ with hb₂
  have hb₂T₁ : b₂ ∈ T₁ := by
    have hu : a₁ * t₁⁻¹ * a₁⁻¹ ∈ T₁ :=
      (Subgroup.mem_normalizer_iff.1 ha₁N₁ _).1 (T₁.inv_mem ht₁T₁)
    have e : b₂ = t₁ * (a₁ * t₁⁻¹ * a₁⁻¹) := by rw [hb₂]; group
    rw [e]
    exact T₁.mul_mem ht₁T₁ hu
  have hb₂N : b₂ ∈ Subgroup.normalizer (T : Set G) := hcent _ hb₂c
  have hb₂1 : b₂ ≠ 1 := by
    intro h1
    apply ht₁N
    refine hcent _ ?_
    have e : t₁ * a₁ = a₁ * t₁ := by
      calc t₁ * a₁ = (t₁ * a₁ * t₁⁻¹ * a₁⁻¹) * (a₁ * t₁) := by group
        _ = a₁ * t₁ := by rw [← hb₂, h1, one_mul]
    exact e.symm
  have hσN₁ : E.Φ (M.d 1) ∈ Subgroup.normalizer (T₁ : Set G) := (hD _).1 (M.d_mem 1)
  have hσN : E.Φ (M.d 1) ∈ Subgroup.normalizer (T : Set G) := E.mem _
  set σ := E.Φ (M.d 1) with hσ
  set x := σ * t₁ * σ⁻¹ with hx
  have hxT₁ : x ∈ T₁ := (Subgroup.mem_normalizer_iff.1 hσN₁ t₁).1 ht₁T₁
  have hxN : x ∉ Subgroup.normalizer (T : Set G) := by
    intro hxN
    apply ht₁N
    have e : t₁ = σ⁻¹ * x * σ := by rw [hx]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hσN) hxN) hσN
  have hy := inv_mul_mem_normIn h h8 ht₁T₁ hxT₁ ht₁N hxN
  have hya : (t₁⁻¹ * x) * a₁ = a₁ * (t₁⁻¹ * x) := (h.comm_A_B ha₁A hy).symm
  have hσa' : σ * a₁ * σ⁻¹ = a₁ := by rw [hσa]; group
  have hσb₂ : σ * b₂ = b₂ * σ := by
    have e1 : σ * b₂ * σ⁻¹ = x * a₁ * x⁻¹ * a₁⁻¹ := by
      calc σ * b₂ * σ⁻¹ = (σ * t₁ * σ⁻¹) * (σ * a₁ * σ⁻¹) * (σ * t₁ * σ⁻¹)⁻¹ *
            (σ * a₁ * σ⁻¹)⁻¹ := by rw [hb₂]; group
        _ = x * a₁ * x⁻¹ * a₁⁻¹ := by rw [hσa', ← hx]
    have e2 : x * a₁ * x⁻¹ * a₁⁻¹ = b₂ := by
      calc x * a₁ * x⁻¹ * a₁⁻¹ = t₁ * ((t₁⁻¹ * x) * a₁) * (t₁⁻¹ * x)⁻¹ * t₁⁻¹ * a₁⁻¹ := by
            group
        _ = t₁ * (a₁ * (t₁⁻¹ * x)) * (t₁⁻¹ * x)⁻¹ * t₁⁻¹ * a₁⁻¹ := by rw [hya]
        _ = b₂ := by rw [hb₂]; group
    calc σ * b₂ = (σ * b₂ * σ⁻¹) * σ := by group
      _ = b₂ * σ := by rw [e1, e2]
  obtain ⟨β'', hβ''⟩ := E.surj b₂ hb₂N
  have hβ''B : β'' ∈ M.B0 := (hB _).2 (by rw [hβ'']; exact hb₂T₁)
  have hσβ : M.d 1 * β'' = β'' * M.d 1 := E.inj (by rw [map_mul, map_mul, hβ'']; exact hσb₂)
  have hb₂b₁ : b₂ = b₁ := by
    rcases M.sig_fix β'' hβ''B hσβ with h1 | h1
    · exact absurd (by rw [← hβ'', h1, map_one]) hb₂1
    · rw [← hβ'', h1]
  have hab : a₁ * b₁ = b₁ * a₁ := h.comm_A_B ha₁A hb₁B
  have hc : t * b₁ * t⁻¹ = t₁ * a₁ * t₁⁻¹ := by
    have e1 : t * b₁ * t⁻¹ = a₁ * b₁ := by rw [ha₁def]; group
    have e2 : t₁ * a₁ * t₁⁻¹ = b₂ * a₁ := by rw [hb₂]; group
    rw [e1, e2, hb₂b₁, hab]
  have hc1 : t * b₁ * t⁻¹ ≠ 1 := fun h' => hb₁1 (by
    have e : b₁ = t⁻¹ * (t * b₁ * t⁻¹) * t := by group
    rw [e, h', mul_one, inv_mul_cancel])
  obtain ⟨s, hs⟩ := h.conj
  have hmem1 : t * b₁ * t⁻¹ ∈ conjSubgroup (t * s) T := by
    rw [← conjSubgroup_conjSubgroup, ← hs, mem_conjSubgroup]
    simpa [mul_assoc] using hb₁T₁
  have hmem2 : t * b₁ * t⁻¹ ∈ conjSubgroup t₁ T := by
    rw [hc, mem_conjSubgroup]
    simpa [mul_assoc] using ha₁T
  have hT2 : conjSubgroup t T₁ = conjSubgroup t₁ T := by
    rw [hs, conjSubgroup_conjSubgroup]
    exact inter_unique h.wc hmem1 hmem2 hc1
  have htt : t * t = 1 := elemAbelian_mul_self h.wc.1 htT
  have ht₁t₁ : t₁ * t₁ = 1 := elemAbelian_mul_self h.elemAbelian₁ ht₁T₁
  have htTT : conjSubgroup t T = T :=
    mem_normalizer_iff_conjSubgroup_eq.1 (Subgroup.le_normalizer htT)
  refine ⟨t * t₁ * t, ?_, ?_⟩
  · rw [← conjSubgroup_conjSubgroup, htTT, ← conjSubgroup_conjSubgroup, ← hT2,
      conjSubgroup_conjSubgroup, htt, conjSubgroup_one]
  · rw [← conjSubgroup_conjSubgroup, hT2, conjSubgroup_conjSubgroup, mul_assoc, ht₁t₁, mul_one,
      htTT]

end CFSG.CGT.A8S.L2
