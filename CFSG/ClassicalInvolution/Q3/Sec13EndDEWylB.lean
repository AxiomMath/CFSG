module

public import CFSG.ClassicalInvolution.Q3.Sec13EndDEWylA
public import CFSG.ClassicalInvolution.Q3.Sec13EndDEQ2

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

open Classical in
@[expose] noncomputable def dewStar (K L : Subgroup G) : Subgroup G :=
  if hk : ∃ k ∈ K, ∃ v : G, IsUniqueInvolution L v ∧ k * v ≠ v * k then conjSub hk.choose L
  else L

structure DewPair (Ω : Set (Subgroup G)) (K L : Subgroup G) (u v : G) : Prop where
  memK : K ∈ Ω
  memL : L ∈ Ω
  invK : IsUniqueInvolution K u
  invL : IsUniqueInvolution L v
  ne : u ≠ v

structure DewTwins (Ω : Set (Subgroup G)) (K J : Subgroup G) (u : G) : Prop where
  memK : K ∈ Ω
  memJ : J ∈ Ω
  invK : IsUniqueInvolution K u
  invJ : IsUniqueInvolution J u
  ne : K ≠ J

theorem DewPair.symm {Ω : Set (Subgroup G)} {K L : Subgroup G} {u v : G}
    (h : DewPair Ω K L u v) : DewPair Ω L K v u :=
  ⟨h.memL, h.memK, h.invL, h.invK, h.ne.symm⟩

theorem DewTwins.symm {Ω : Set (Subgroup G)} {K J : Subgroup G} {u : G}
    (h : DewTwins Ω K J u) : DewTwins Ω J K u :=
  ⟨h.memJ, h.memK, h.invJ, h.invK, h.ne.symm⟩

@[expose] def IsElationOf (Ω : Set (Subgroup G)) (u : G) (φ : G → ZMod 2) (k : G) : Prop :=
  ∀ x ∈ zGroup Ω, k * x * k⁻¹ = if φ x = 0 then x else u * x

@[expose] def dewDelta (K J : Subgroup G) : Subgroup G :=
  (K ⊔ J) ⊓ pCore 2 G

@[expose] noncomputable def dewTau (K J M : Subgroup G) : Subgroup G :=
  dewStar J (dewStar K M)

@[expose] def dewKer (Ω : Set (Subgroup G)) (u : G) : Subgroup G :=
  Subgroup.centralizer ({u} : Set G) ⊓ ⨅ M ∈ dew1V Ω u, Subgroup.normalizer (M : Set G)

namespace DE4Hyp

variable {Ω : Set (Subgroup G)} (h : DE4Hyp Ω)
include h

theorem ncard_dew1V {K : Subgroup G} {u : G} (hK : K ∈ Ω) (hu : IsUniqueInvolution K u) :
    (dew1V Ω u).ncard = 4 := by
  rw [dew1V_eq_twinSet hK hu]
  exact h.twin4 K hK

theorem exists_mem_dew1V {u : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) : ∃ K, K ∈ dew1V Ω u := by
  obtain ⟨K, hK, hKu⟩ := (h.mem_zGroup_iff.mp hu).resolve_left hu1
  exact ⟨K, hK, hKu⟩

theorem conj_eq_or_mul {K : Subgroup G} {u : G} (hK : K ∈ Ω) (hu : IsUniqueInvolution K u)
    {k x : G} (hk : k ∈ K) (hx : x ∈ zGroup Ω) : k * x * k⁻¹ = x ∨ k * x * k⁻¹ = u * x := by
  have h1 := h.dComm_mem_zpowers hK hu hx hk
  have h2 := det_tw_eq_one_or_of_mem_zpowers hu.sq hu.ne_one h1
  unfold dComm at h2
  rcases h2 with h2 | h2
  · left
    have h3 : k * x * k⁻¹ * x⁻¹ = 1 := by
      have := congrArg (fun t => t⁻¹) h2
      simp only [inv_one] at this
      rw [← this]
      group
    calc k * x * k⁻¹ = (k * x * k⁻¹ * x⁻¹) * x := by group
      _ = x := by rw [h3, one_mul]
  · right
    have hu1 : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu.sq
    have h3 : k * x * k⁻¹ * x⁻¹ = u := by
      have := congrArg (fun t => t⁻¹) h2
      simp only [hu1] at this
      rw [← this]
      group
    calc k * x * k⁻¹ = (k * x * k⁻¹ * x⁻¹) * x := by group
      _ = u * x := by rw [h3]

theorem card_inf_centralizer_dew {K : Subgroup G} {u v : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) (hv : v ∈ zGroup Ω) (hvu : v ∉ Subgroup.zpowers u) :
    Nat.card ↥(K ⊓ Subgroup.centralizer ({v} : Set G)) = 4 ∧
      IsCyclic ↥(K ⊓ Subgroup.centralizer ({v} : Set G)) := by
  obtain ⟨h1, h2, -⟩ := h.det_tw_core hK hu hv hvu
  exact ⟨h1, h2⟩

theorem inf_centralizer_le_normalizer {K : Subgroup G} {u v : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) (hv : v ∈ zGroup Ω) (hvu : v ∉ Subgroup.zpowers u)
    {M : Subgroup G} (hM : M ∈ dew1V Ω v ∨ M ∈ dew1V Ω (u * v)) :
    K ⊓ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (M : Set G) := by
  rcases hM with hM | hM
  · obtain ⟨-, -, hn⟩ := h.det_tw_core hK hu hv hvu
    refine hn M hM.1 ?_ hM.2
    rintro rfl
    exact hvu (hu.eq hM.2 ▸ Subgroup.mem_zpowers u)
  · have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
    have huvD : u * v ∈ zGroup Ω := (zGroup Ω).mul_mem huD hv
    have huv : u * v ∉ Subgroup.zpowers u := by
      intro hmem
      apply hvu
      have : v = u⁻¹ * (u * v) := by group
      rw [this]
      exact (Subgroup.zpowers u).mul_mem ((Subgroup.zpowers u).inv_mem (Subgroup.mem_zpowers u))
        hmem
    obtain ⟨-, -, hn⟩ := h.det_tw_core hK hu huvD huv
    have heq : K ⊓ Subgroup.centralizer ({v} : Set G) =
        K ⊓ Subgroup.centralizer ({u * v} : Set G) := by
      ext k
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨hk, hkv⟩
        refine ⟨hk, ?_⟩
        have hku' : k * u * k⁻¹ = u := conj_of_mem_mem hu hk (Or.inr rfl)
        have hku : k * u = u * k := by rw [mul_inv_eq_iff_eq_mul] at hku'; exact hku'
        calc k * (u * v) = (k * u) * v := by group
          _ = (u * k) * v := by rw [hku]
          _ = u * (k * v) := by group
          _ = u * (v * k) := by rw [hkv]
          _ = u * v * k := by group
      · rintro ⟨hk, hkv⟩
        refine ⟨hk, ?_⟩
        have hku' : k * u * k⁻¹ = u := conj_of_mem_mem hu hk (Or.inr rfl)
        have hku : k * u = u * k := by rw [mul_inv_eq_iff_eq_mul] at hku'; exact hku'
        have : u * (k * v) = u * (v * k) := by
          calc u * (k * v) = (u * k) * v := by group
            _ = (k * u) * v := by rw [hku]
            _ = k * (u * v) := by group
            _ = u * v * k := hkv
            _ = u * (v * k) := by group
        exact mul_left_cancel this
    rw [heq]
    exact hn M hM.1 (by
      rintro rfl
      have := hu.eq hM.2
      have hv1 : v = 1 := by
        have h2 : u * 1 = u * v := by rw [mul_one]; exact this
        exact (mul_left_cancel h2).symm
      exact hvu (by rw [hv1]; exact Subgroup.one_mem _)) hM.2

private theorem dewb1_conj_pair {K : Subgroup G} {u v k : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) (hv : v ∈ zGroup Ω) (hk : k ∈ K) (hkv : k * v ≠ v * k) :
    k * v * k⁻¹ = u * v ∧ k * (u * v) * k⁻¹ = v := by
  have hkv_eq : k * v * k⁻¹ = u * v := by
    rcases h.conj_eq_or_mul hK hu hk hv with h1 | h1
    · exfalso
      apply hkv
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1
    · exact h1
  have hku : k * u * k⁻¹ = u := conj_of_mem_mem hu hk (Or.inr rfl)
  refine ⟨hkv_eq, ?_⟩
  calc k * (u * v) * k⁻¹ = (k * u * k⁻¹) * (k * v * k⁻¹) := by group
    _ = u * (u * v) := by rw [hku, hkv_eq]
    _ = v := by rw [← mul_assoc, hu.sq, one_mul]

theorem conjSub_image_dew1V {K : Subgroup G} {u v : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) (hv : v ∈ zGroup Ω) (hvu : v ∉ Subgroup.zpowers u) {k : G}
    (hk : k ∈ K) (hkv : k * v ≠ v * k) :
    conjSub k '' dew1V Ω v = dew1V Ω (u * v) ∧ conjSub k '' dew1V Ω (u * v) = dew1V Ω v := by
  obtain ⟨hkv1, hkuv1⟩ := h.dewb1_conj_pair hK hu hv hk hkv
  have hv1 : v ≠ 1 := fun h1 => hvu (by rw [h1]; exact Subgroup.one_mem _)
  have huvu : u * v ∉ Subgroup.zpowers u := by
    intro hmem
    apply hvu
    have e : v = u⁻¹ * (u * v) := by group
    rw [e]
    exact (Subgroup.zpowers u).mul_mem ((Subgroup.zpowers u).inv_mem (Subgroup.mem_zpowers u)) hmem
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
  have huvD : u * v ∈ zGroup Ω := (zGroup Ω).mul_mem huD hv
  have huv1 : u * v ≠ 1 := fun h1 => huvu (by rw [h1]; exact Subgroup.one_mem _)
  obtain ⟨L, hL⟩ := h.exists_mem_dew1V hv hv1
  obtain ⟨L', hL'⟩ := h.exists_mem_dew1V huvD huv1
  have hc1 : (dew1V Ω v).ncard = 4 := h.ncard_dew1V hL.1 hL.2
  have hc2 : (dew1V Ω (u * v)).ncard = 4 := h.ncard_dew1V hL'.1 hL'.2
  have hinj := conjSub_injective k
  have hmap1 : ∀ M ∈ dew1V Ω v, conjSub k M ∈ dew1V Ω (u * v) := fun M hM =>
    ⟨h.hyp.conjInvariant k M hM.1, by rw [← hkv1]; exact hM.2.conj k⟩
  have hmap2 : ∀ M ∈ dew1V Ω (u * v), conjSub k M ∈ dew1V Ω v := fun M hM =>
    ⟨h.hyp.conjInvariant k M hM.1, by rw [← hkuv1]; exact hM.2.conj k⟩
  have hsub1 : conjSub k '' dew1V Ω v ⊆ dew1V Ω (u * v) := by
    rintro _ ⟨M, hM, rfl⟩
    exact hmap1 M hM
  have hsub2 : conjSub k '' dew1V Ω (u * v) ⊆ dew1V Ω v := by
    rintro _ ⟨M, hM, rfl⟩
    exact hmap2 M hM
  have hi1 : (conjSub k '' dew1V Ω v).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ hinj, hc1]
  have hi2 : (conjSub k '' dew1V Ω (u * v)).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ hinj, hc2]
  exact ⟨Set.eq_of_subset_of_ncard_le hsub1 (by omega),
    Set.eq_of_subset_of_ncard_le hsub2 (by omega)⟩

theorem le_normalizer_of_dew1V {K : Subgroup G} {u : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) {M : Subgroup G} (hM : M ∈ dew1V Ω u) :
    K ≤ Subgroup.normalizer (M : Set G) := by
  by_cases hMK : M = K
  · subst hMK
    exact Subgroup.le_normalizer
  · have hc := h.commutes_of_mem_twinSet hK ⟨hM.1, u, hu, hM.2⟩ hMK
    intro k hk
    exact mem_normalizer_iff_conjSub_eq.mpr (conjSub_eq_of_mem_of_commutes hk hc)

private theorem dewb1_notin_zpowers {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v) :
    v ∉ Subgroup.zpowers u := by
  intro hv
  rcases det_tw_eq_one_or_of_mem_zpowers sp.invK.sq sp.invK.ne_one hv with h1 | h1
  · exact sp.invL.ne_one h1
  · exact sp.ne h1.symm

theorem dewStar_eq {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v) {k : G} (hk : k ∈ K)
    (hkv : k * v ≠ v * k) : dewStar K L = conjSub k L := by
  classical
  have hex : ∃ k ∈ K, ∃ v : G, IsUniqueInvolution L v ∧ k * v ≠ v * k :=
    ⟨k, hk, v, sp.invL, hkv⟩
  have hvD : v ∈ zGroup Ω := dew1_involution_mem h.toDEHyp sp.memL sp.invL
  have hvu : v ∉ Subgroup.zpowers u := dewb1_notin_zpowers h sp
  unfold dewStar
  rw [dif_pos hex]
  obtain ⟨hc, v', hv', hcv'⟩ := hex.choose_spec
  have hvv : v' = v := hv'.eq sp.invL
  subst hvv
  set c := hex.choose with hcdef
  have hconj_u : ∀ y ∈ K, y * u * y⁻¹ = u := fun y hy => conj_of_mem_mem sp.invK hy (Or.inr rfl)
  have hmove : ∀ y ∈ K, y * v' ≠ v' * y → y * v' * y⁻¹ = u * v' := by
    intro y hy hyv
    rcases conj_eq_or_mul h sp.memK sp.invK hy hvD with h1 | h1
    · exact absurd (by rw [mul_inv_eq_iff_eq_mul] at h1; exact h1) hyv
    · exact h1
  have hck := hmove c hc hcv'
  have hkk := hmove k hk hkv
  have h7 : c⁻¹ * u * c = u := by
    have := hconj_u c⁻¹ (K.inv_mem hc)
    simpa using this
  have hcinv : c⁻¹ * v' * c = u * v' := by
    have h6 : v' = c⁻¹ * (u * v') * c := by rw [← hck]; group
    calc c⁻¹ * v' * c = u * (u * (c⁻¹ * v' * c)) := by
          rw [← mul_assoc, sp.invK.sq, one_mul]
      _ = u * (c⁻¹ * (u * v') * c) := by
          congr 1
          calc u * (c⁻¹ * v' * c) = (c⁻¹ * u * c) * (c⁻¹ * v' * c) := by rw [h7]
            _ = c⁻¹ * (u * v') * c := by group
      _ = u * v' := by rw [← h6]
  have hmem : c⁻¹ * k ∈ K ⊓ Subgroup.centralizer ({v'} : Set G) := by
    refine ⟨K.mul_mem (K.inv_mem hc) hk, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h8 : c⁻¹ * (k * v' * k⁻¹) * c = v' := by
      rw [hkk]
      calc c⁻¹ * (u * v') * c = (c⁻¹ * u * c) * (c⁻¹ * v' * c) := by group
        _ = u * (u * v') := by rw [h7, hcinv]
        _ = v' := by rw [← mul_assoc, sp.invK.sq, one_mul]
    calc c⁻¹ * k * v' = (c⁻¹ * (k * v' * k⁻¹) * c) * (c⁻¹ * k) := by group
      _ = v' * (c⁻¹ * k) := by rw [h8]
  have hn := inf_centralizer_le_normalizer h sp.memK sp.invK hvD hvu
    (Or.inl ⟨sp.memL, sp.invL⟩) hmem
  have hnorm : conjSub (c⁻¹ * k) L = L := mem_normalizer_iff_conjSub_eq.mp hn
  calc conjSub c L = conjSub c (conjSub (c⁻¹ * k) L) := by rw [hnorm]
    _ = conjSub (c * (c⁻¹ * k)) L := (conjSub_mul c (c⁻¹ * k) L).symm
    _ = conjSub k L := by rw [mul_inv_cancel_left]

theorem exists_not_comm_of_dewPair {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v) :
    ∃ k ∈ K, k * v ≠ v * k := by
  have hvD : v ∈ zGroup Ω := dew1_involution_mem h.toDEHyp sp.memL sp.invL
  have hcore := h.det_tw_core sp.memK sp.invK hvD (dewb1_notin_zpowers h sp)
  by_contra hcon
  push Not at hcon
  have hle : K ≤ Subgroup.centralizer ({v} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcon k hk)
  rw [inf_eq_left.mpr hle] at hcore
  have h8 := h.card K sp.memK
  have h4 := hcore.1
  omega

theorem dewStar_mem_dew1V {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v) :
    dewStar K L ∈ dew1V Ω (u * v) := by
  obtain ⟨k, hk, hkv⟩ := h.exists_not_comm_of_dewPair sp
  have hvD : v ∈ zGroup Ω := dew1_involution_mem h.toDEHyp sp.memL sp.invL
  have hvu : v ∉ Subgroup.zpowers u := dewb1_notin_zpowers h sp
  rw [h.dewStar_eq sp hk hkv]
  have hmem : conjSub k L ∈ conjSub k '' dew1V Ω v := Set.mem_image_of_mem _ ⟨sp.memL, sp.invL⟩
  rw [(h.conjSub_image_dew1V sp.memK sp.invK hvD hvu hk hkv).1] at hmem
  exact hmem

theorem dewStar_dewStar {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v) :
    dewStar K (dewStar K L) = L := by
  have hvD : v ∈ zGroup Ω := dew1_involution_mem h.toDEHyp sp.memL sp.invL
  have hvu : v ∉ Subgroup.zpowers u := dewb1_notin_zpowers h sp
  have hv1 : v ≠ 1 := fun h1 => hvu (by rw [h1]; exact Subgroup.one_mem _)
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp sp.memK sp.invK
  have hN : dewStar K L ∈ dew1V Ω (u * v) := h.dewStar_mem_dew1V sp
  have hne : u ≠ u * v := fun h1 =>
    hv1 (mul_left_cancel (a := u) (by rw [mul_one]; exact h1)).symm
  have sp' : DewPair Ω K (dewStar K L) u (u * v) :=
    ⟨sp.memK, hN.1, sp.invK, hN.2, hne⟩
  obtain ⟨k, hk, hkv⟩ := h.exists_not_comm_of_dewPair sp
  obtain ⟨-, hkuv⟩ := h.dewb1_conj_pair sp.memK sp.invK hvD hk hkv
  have hkuv_ne : k * (u * v) ≠ u * v * k := by
    intro heq
    have h1 : k * (u * v) * k⁻¹ = u * v := by
      rw [heq]
      group
    rw [hkuv] at h1
    have h2 : u * v = v := h1.symm
    apply sp.invK.ne_one
    calc u = u * v * v⁻¹ := by group
      _ = v * v⁻¹ := by rw [h2]
      _ = 1 := by group
  have hkZ : k ∉ Subgroup.zpowers u := by
    intro hmem
    rcases det_tw_eq_one_or_of_mem_zpowers sp.invK.sq sp.invK.ne_one hmem with h1 | h1
    · apply hkv
      rw [h1, one_mul, mul_one]
    · apply hkv
      rw [h1]
      exact h.zGroup_comm u huD v hvD
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hnf⟩ :=
    exists_q8_gen sp.invK (h.isQuatSub_of_mem sp.memK) (h.card K sp.memK)
  have hQ : Q8Data K u i j := ⟨sp.invK, hi, hj, hii, hjj, hji, hnf⟩
  have hkk : k * k = u := det_tw_q8_sq hQ hk hkZ
  calc dewStar K (dewStar K L) = conjSub k (dewStar K L) := h.dewStar_eq sp' hk hkuv_ne
    _ = conjSub k (conjSub k L) := by rw [h.dewStar_eq sp hk hkv]
    _ = conjSub (k * k) L := (conjSub_mul k k L).symm
    _ = conjSub u L := by rw [hkk]
    _ = L := mem_normalizer_iff_conjSub_eq.mp (h.dNorm L sp.memL huD)

theorem conjSub_dewStar {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v) (g : G) :
    conjSub g (dewStar K L) = dewStar (conjSub g K) (conjSub g L) := by
  obtain ⟨k, hk, hkv⟩ := h.exists_not_comm_of_dewPair sp
  have sp' : DewPair Ω (conjSub g K) (conjSub g L) (g * u * g⁻¹) (g * v * g⁻¹) :=
    ⟨h.hyp.conjInvariant g K sp.memK, h.hyp.conjInvariant g L sp.memL, sp.invK.conj g,
      sp.invL.conj g, fun heq => sp.ne (mul_left_cancel (mul_right_cancel heq))⟩
  have hk' : g * k * g⁻¹ ∈ conjSub g K := conj_mem_conjSub hk
  have hkv' : g * k * g⁻¹ * (g * v * g⁻¹) ≠ g * v * g⁻¹ * (g * k * g⁻¹) := by
    intro heq
    apply hkv
    have e1 : g * k * g⁻¹ * (g * v * g⁻¹) = g * (k * v) * g⁻¹ := by group
    have e2 : g * v * g⁻¹ * (g * k * g⁻¹) = g * (v * k) * g⁻¹ := by group
    rw [e1, e2] at heq
    exact mul_left_cancel (mul_right_cancel heq)
  rw [h.dewStar_eq sp hk hkv, h.dewStar_eq sp' hk' hkv']
  calc conjSub g (conjSub k L) = conjSub (g * k) L := (conjSub_mul g k L).symm
    _ = conjSub (g * k * g⁻¹ * g) L := by rw [inv_mul_cancel_right]
    _ = conjSub (g * k * g⁻¹) (conjSub g L) := conjSub_mul _ _ _

theorem conjSub_eq_or_dewStar {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v) {k : G}
    (hk : k ∈ K) : conjSub k L = L ∨ conjSub k L = dewStar K L := by
  by_cases hkv : k * v = v * k
  · have hvD : v ∈ zGroup Ω := dew1_involution_mem h.toDEHyp sp.memL sp.invL
    have hvu : v ∉ Subgroup.zpowers u := dewb1_notin_zpowers h sp
    have hN : k ∈ Subgroup.normalizer (L : Set G) :=
      inf_centralizer_le_normalizer h sp.memK sp.invK hvD hvu (Or.inl ⟨sp.memL, sp.invL⟩)
        (show k ∈ K ⊓ Subgroup.centralizer ({v} : Set G) from
          ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr hkv⟩)
    exact Or.inl (mem_normalizer_iff_conjSub_eq.mp hN)
  · exact Or.inr (h.dewStar_eq sp hk hkv).symm

theorem mem_normalizer_iff_commute {K L : Subgroup G} {u v : G} (sp : DewPair Ω K L u v)
    {k : G} (hk : k ∈ K) : k ∈ Subgroup.normalizer (L : Set G) ↔ k * v = v * k := by
  have hvD : v ∈ zGroup Ω := dew1_involution_mem h.toDEHyp sp.memL sp.invL
  have hvu : v ∉ Subgroup.zpowers u := dewb1_notin_zpowers h sp
  constructor
  · intro hkN
    have hc : k * v * k⁻¹ = v := sp.invL.conj_eq (mem_normalizer_iff_conjSub_eq.mp hkN)
    rw [mul_inv_eq_iff_eq_mul] at hc
    exact hc
  · intro hkv
    exact inf_centralizer_le_normalizer h sp.memK sp.invK hvD hvu (Or.inl ⟨sp.memL, sp.invL⟩)
      (show k ∈ K ⊓ Subgroup.centralizer ({v} : Set G) from
        ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr hkv⟩)

omit h in
private theorem dewb2_mem_sup {K J : Subgroup G} (hc : Commutes K J) {x : G} (hx : x ∈ K ⊔ J) :
    ∃ k ∈ K, ∃ j ∈ J, k * j = x := by
  let S : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ j ∈ J, k * j = x}
      one_mem' := ⟨1, K.one_mem, 1, J.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨k1, hk1, j1, hj1, rfl⟩ ⟨k2, hk2, j2, hj2, rfl⟩
        refine ⟨k1 * k2, K.mul_mem hk1 hk2, j1 * j2, J.mul_mem hj1 hj2, ?_⟩
        calc k1 * k2 * (j1 * j2) = k1 * (k2 * j1) * j2 := by group
          _ = k1 * (j1 * k2) * j2 := by rw [hc k2 hk2 j1 hj1]
          _ = k1 * j1 * (k2 * j2) := by group
      inv_mem' := by
        rintro _ ⟨k, hk, j, hj, rfl⟩
        have hcj : j⁻¹ * k⁻¹ = k⁻¹ * j⁻¹ := by
          rw [← mul_inv_rev k j, hc k hk j hj, mul_inv_rev j k]
        refine ⟨k⁻¹, K.inv_mem hk, j⁻¹, J.inv_mem hj, ?_⟩
        rw [mul_inv_rev, hcj] }
  have hKS : K ≤ S := by
    intro k hk
    exact ⟨k, hk, 1, J.one_mem, mul_one k⟩
  have hJS : J ≤ S := by
    intro j hj
    exact ⟨1, K.one_mem, j, hj, one_mul j⟩
  obtain ⟨k, hk, j, hj, hkj⟩ := (sup_le hKS hJS : K ⊔ J ≤ S) hx
  exact ⟨k, hk, j, hj, hkj⟩

omit h in
private theorem dewb2_ne_mul {u v : G} (hv : v ≠ 1) : u ≠ u * v := by
  intro h
  apply hv
  have h' : u * 1 = u * v := by rw [mul_one]; exact h
  exact (mul_left_cancel h').symm

omit h in
private theorem dewb2_u_mul_ne {u : G} (hu1 : u ≠ 1) (x : G) : u * x ≠ x := by
  intro h
  apply hu1
  exact mul_right_cancel (h.trans (one_mul x).symm)

omit h in
private theorem dewb2_coord {E : Subgroup G} {e : Fin 3 → G} (he : TL4.E8Basis E e)
    {ψ : G → ZMod 2} (h1 : ψ 1 = 0) (hadd : ∀ x ∈ E, ∀ y ∈ E, ψ (x * y) = ψ x + ψ y)
    (h0 : ψ (e 0) = 0) (v : Fin 3 → ZMod 2) :
    ψ (TL4.e8Coord e v) = v 1 * ψ (e 1) + v 2 * ψ (e 2) := by
  have hadd' : ∀ a b : Fin 3 → ZMod 2,
      ψ (TL4.e8Coord e (a + b)) = ψ (TL4.e8Coord e a) + ψ (TL4.e8Coord e b) := by
    intro a b
    rw [TL4.e8Coord_add he a b]
    exact hadd _ (TL4.e8Coord_mem he a) _ (TL4.e8Coord_mem he b)
  have hs0 : ∀ c : ZMod 2, ψ (TL4.e8Coord e (Pi.single 0 c)) = 0 := by
    intro c
    rcases TL4.zmod_two_cases c with rfl | rfl
    · rw [Pi.single_zero, TL4.e8Coord_zero, h1]
    · rw [TL4.e8Coord_single, h0]
  have hs1 : ∀ c : ZMod 2, ψ (TL4.e8Coord e (Pi.single 1 c)) = c * ψ (e 1) := by
    intro c
    rcases TL4.zmod_two_cases c with rfl | rfl
    · rw [Pi.single_zero, TL4.e8Coord_zero, h1, zero_mul]
    · rw [TL4.e8Coord_single, one_mul]
  have hs2 : ∀ c : ZMod 2, ψ (TL4.e8Coord e (Pi.single 2 c)) = c * ψ (e 2) := by
    intro c
    rcases TL4.zmod_two_cases c with rfl | rfl
    · rw [Pi.single_zero, TL4.e8Coord_zero, h1, zero_mul]
    · rw [TL4.e8Coord_single, one_mul]
  have hdec : v = (Pi.single 0 (v 0) : Fin 3 → ZMod 2) + (Pi.single 1 (v 1) : Fin 3 → ZMod 2) +
      (Pi.single 2 (v 2) : Fin 3 → ZMod 2) := by
    funext i
    fin_cases i <;> simp
  have hv : ψ (TL4.e8Coord e v) =
      ψ (TL4.e8Coord e ((Pi.single 0 (v 0) : Fin 3 → ZMod 2) +
        (Pi.single 1 (v 1) : Fin 3 → ZMod 2) + (Pi.single 2 (v 2) : Fin 3 → ZMod 2))) := by
    rw [← hdec]
  rw [hv, hadd', hadd', hs0, hs1, hs2, zero_add]

omit h in
private theorem dewb2_eq_of_coord [Finite G] {E : Subgroup G} {e : Fin 3 → G}
    (he : TL4.E8Basis E e) {ψ ψ' : G → ZMod 2} (h1 : ψ 1 = 0) (h1' : ψ' 1 = 0)
    (hadd : ∀ x ∈ E, ∀ y ∈ E, ψ (x * y) = ψ x + ψ y)
    (hadd' : ∀ x ∈ E, ∀ y ∈ E, ψ' (x * y) = ψ' x + ψ' y)
    (hoff : ∀ x, x ∉ E → ψ x = 0) (hoff' : ∀ x, x ∉ E → ψ' x = 0)
    (h0 : ψ (e 0) = 0) (h0' : ψ' (e 0) = 0)
    (h2 : ψ (e 1) = ψ' (e 1)) (h3 : ψ (e 2) = ψ' (e 2)) : ψ = ψ' := by
  funext x
  by_cases hx : x ∈ E
  · obtain ⟨v, rfl⟩ := TL4.exists_e8Coord_eq he hx
    rw [dewb2_coord he h1 hadd h0 v, dewb2_coord he h1' hadd' h0' v, h2, h3]
  · rw [hoff x hx, hoff' x hx]

omit h in
private theorem dewb2_four : ∀ p x y z : ZMod 2 × ZMod 2, x ≠ (0, 0) → y ≠ (0, 0) →
    z ≠ (0, 0) → x ≠ y → x ≠ z → y ≠ z → p = (0, 0) ∨ p = x ∨ p = y ∨ p = z := by
  intro p x y z
  fin_cases p <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> decide

private theorem dewb2_quot_mem_zpowers {K : Subgroup G} {u : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) {φ : G → ZMod 2} {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K)
    (h1 : IsElationOf Ω u φ k) (h2 : IsElationOf Ω u φ k') : k'⁻¹ * k ∈ Subgroup.zpowers u := by
  have hc : k'⁻¹ * k ∈ K ⊓ Subgroup.centralizer (zGroup Ω : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem hk') hk, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro x hx
    have e1 : k * x * k⁻¹ = k' * x * k'⁻¹ := (h1 x hx).trans (h2 x hx).symm
    have e2 : k'⁻¹ * k * x * (k'⁻¹ * k)⁻¹ = x := by
      calc k'⁻¹ * k * x * (k'⁻¹ * k)⁻¹ = k'⁻¹ * (k * x * k⁻¹) * k' := by group
        _ = k'⁻¹ * (k' * x * k'⁻¹) * k' := by rw [e1]
        _ = x := by group
    have e3 : (k'⁻¹ * k) * x = x * (k'⁻¹ * k) := by
      calc (k'⁻¹ * k) * x = (k'⁻¹ * k * x * (k'⁻¹ * k)⁻¹) * (k'⁻¹ * k) := by group
        _ = x * (k'⁻¹ * k) := by rw [e2]
    exact e3.symm
  rw [h.inf_centralizer_zGroup hK hu] at hc
  exact hc

theorem exists_isElationOf {K : Subgroup G} {u : G} (hK : K ∈ Ω) (hu : IsUniqueInvolution K u)
    {k : G} (hk : k ∈ K) : ∃ φ ∈ DE2Hyp.deq2Dual Ω, φ u = 0 ∧ IsElationOf Ω u φ k := by
  classical
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
  have hu1 : u ≠ 1 := hu.ne_one
  have hconj : ∀ x ∈ zGroup Ω, k * x * k⁻¹ = x ∨ k * x * k⁻¹ = u * x :=
    fun x hx => h.conj_eq_or_mul hK hu hk hx
  let F : G → ZMod 2 := fun x => if x ∈ zGroup Ω ∧ k * x * k⁻¹ ≠ x then 1 else 0
  have hF1 : F 1 = 0 := by
    show (if (1 : G) ∈ zGroup Ω ∧ k * 1 * k⁻¹ ≠ 1 then (1 : ZMod 2) else 0) = 0
    rw [if_neg]
    rintro ⟨-, hne⟩
    exact hne (by group)
  have hFoff : ∀ x, x ∉ zGroup Ω → F x = 0 := by
    intro x hx
    show (if x ∈ zGroup Ω ∧ k * x * k⁻¹ ≠ x then (1 : ZMod 2) else 0) = 0
    rw [if_neg (fun h' => hx h'.1)]
  have hFu : F u = 0 := by
    show (if u ∈ zGroup Ω ∧ k * u * k⁻¹ ≠ u then (1 : ZMod 2) else 0) = 0
    rw [if_neg]
    rintro ⟨-, hne⟩
    exact hne (conj_of_mem_mem hu hk (Or.inr rfl))
  have hFD : ∀ x ∈ zGroup Ω, (F x = 0 ↔ k * x * k⁻¹ = x) := by
    intro x hx
    show (if x ∈ zGroup Ω ∧ k * x * k⁻¹ ≠ x then (1 : ZMod 2) else 0) = 0 ↔ k * x * k⁻¹ = x
    by_cases hc : k * x * k⁻¹ = x
    · rw [if_neg (fun h' => h'.2 hc)]
      exact ⟨fun _ => hc, fun _ => rfl⟩
    · rw [if_pos ⟨hx, hc⟩]
      exact ⟨fun h' => absurd h' one_ne_zero, fun h' => absurd h' hc⟩
  have hF_fix : ∀ x ∈ zGroup Ω, k * x * k⁻¹ = x → F x = 0 :=
    fun x hx hc => (hFD x hx).mpr hc
  have hF_mul : ∀ x ∈ zGroup Ω, k * x * k⁻¹ = u * x → F x = 1 := by
    intro x hx hc
    have hne : k * x * k⁻¹ ≠ x := by
      rw [hc]; exact dewb2_u_mul_ne hu1 x
    show (if x ∈ zGroup Ω ∧ k * x * k⁻¹ ≠ x then (1 : ZMod 2) else 0) = 1
    exact if_pos ⟨hx, hne⟩
  have hFadd : ∀ x ∈ zGroup Ω, ∀ y ∈ zGroup Ω, F (x * y) = F x + F y := by
    intro x hx y hy
    have hxy : x * y ∈ zGroup Ω := (zGroup Ω).mul_mem hx hy
    have hux : u * x = x * u := h.zGroup_comm u huD x hx
    have hmul : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
    rcases hconj x hx with hx1 | hx1 <;> rcases hconj y hy with hy1 | hy1 <;>
      rcases hconj (x * y) hxy with hxy1 | hxy1
    · rw [hF_fix x hx hx1, hF_fix y hy hy1, hF_fix (x * y) hxy hxy1]
      decide
    · exfalso
      rw [hx1, hy1, hxy1] at hmul
      exact dewb2_u_mul_ne hu1 (x * y) hmul
    · exfalso
      rw [hx1, hy1, hxy1] at hmul
      exact dewb2_u_mul_ne hu1 y (mul_left_cancel hmul).symm
    · rw [hF_fix x hx hx1, hF_mul y hy hy1, hF_mul (x * y) hxy hxy1]
      decide
    · exfalso
      rw [hx1, hy1, hxy1] at hmul
      rw [mul_assoc] at hmul
      exact dewb2_u_mul_ne hu1 (x * y) hmul.symm
    · rw [hF_mul x hx hx1, hF_fix y hy hy1, hF_mul (x * y) hxy hxy1]
      decide
    · rw [hF_mul x hx hx1, hF_mul y hy hy1, hF_fix (x * y) hxy hxy1]
      decide
    · exfalso
      have hxyuu : u * x * (u * y) = x * y := by
        calc u * x * (u * y) = u * (x * u) * y := by group
          _ = u * (u * x) * y := by rw [← hux]
          _ = (u * u) * (x * y) := by group
          _ = x * y := by rw [h.zGroup_mul_self u huD, one_mul]
      rw [hx1, hy1, hxy1, hxyuu] at hmul
      exact dewb2_u_mul_ne hu1 (x * y) hmul
  refine ⟨F, ⟨hF1, hFoff, fun x hx y hy => hFadd x hx y hy⟩, hFu, ?_⟩
  intro x hx
  by_cases hc : k * x * k⁻¹ = x
  · rw [if_pos ((hFD x hx).mpr hc)]
    exact hc
  · have hc' : k * x * k⁻¹ = u * x := (hconj x hx).resolve_left hc
    rw [if_neg (fun h' => hc ((hFD x hx).mp h')), hc']

theorem exists_mem_isElationOf {K : Subgroup G} {u : G} (hK : K ∈ Ω)
    (hu : IsUniqueInvolution K u) {φ : G → ZMod 2} (hφ : φ ∈ DE2Hyp.deq2Dual Ω) (hφu : φ u = 0) :
    ∃ k ∈ K, IsElationOf Ω u φ k := by
  classical
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hK hu
  have hu1 : u ≠ 1 := hu.ne_one
  obtain ⟨e, he, he0⟩ := h.det_tw_basis huD hu1
  obtain ⟨a, b, ha, hb, haa, hbb, hba, -⟩ :=
    exists_q8_gen hu (h.isQuatSub_of_mem hK) (h.card K hK)
  have hau : a * u = u * a := mul_inv_eq_iff_eq_mul.mp (conj_of_mem_mem hu ha (Or.inr rfl))
  have hbu : b * u = u * b := mul_inv_eq_iff_eq_mul.mp (conj_of_mem_mem hu hb (Or.inr rfl))
  obtain ⟨φa, hφa, hφa0, hela⟩ := h.exists_isElationOf hK hu ha
  obtain ⟨φb, hφb, hφb0, helb⟩ := h.exists_isElationOf hK hu hb
  obtain ⟨φab, hφab, hφab0, helab⟩ := h.exists_isElationOf hK hu (K.mul_mem ha hb)
  have hzero : (0 : G → ZMod 2) ∈ DE2Hyp.deq2Dual Ω :=
    ⟨rfl, fun _ _ => rfl, fun _ _ _ _ => (add_zero (0 : ZMod 2)).symm⟩
  have hzu : (0 : G → ZMod 2) u = 0 := rfl
  have helz : IsElationOf Ω u (0 : G → ZMod 2) 1 := by
    intro x _
    simp
  have uniq : ∀ ψ ψ' : G → ZMod 2, ψ ∈ DE2Hyp.deq2Dual Ω → ψ' ∈ DE2Hyp.deq2Dual Ω →
      ψ u = 0 → ψ' u = 0 → ψ (e 1) = ψ' (e 1) → ψ (e 2) = ψ' (e 2) → ψ = ψ' := by
    intro ψ ψ' hψ hψ' hψu hψ'u h1 h2
    obtain ⟨hψ1, hψoff, hψadd⟩ := hψ
    obtain ⟨hψ'1, hψ'off, hψ'add⟩ := hψ'
    refine dewb2_eq_of_coord he hψ1 hψ'1 (fun x hx y hy => hψadd x hx y hy)
      (fun x hx y hy => hψ'add x hx y hy) (fun x hx => hψoff x hx) (fun x hx => hψ'off x hx)
      ?_ ?_ h1 h2
    · rw [he0]; exact hψu
    · rw [he0]; exact hψ'u
  have hsqab : a * b * (a * b) = u := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (u * (a * b)) * b := by rw [hba]
      _ = (a * u) * (a * b) * b := by group
      _ = (u * a) * (a * b) * b := by rw [hau]
      _ = u * (a * a) * (b * b) := by group
      _ = u * u * u := by rw [haa, hbb]
      _ = u := by rw [hu.sq, one_mul]
  have hab_a : a * b * a = b := by
    calc a * b * a = a * (b * a) := by group
      _ = a * (u * (a * b)) := by rw [hba]
      _ = (a * u) * (a * b) := by group
      _ = (u * a) * (a * b) := by rw [hau]
      _ = u * (a * a) * b := by group
      _ = u * u * b := by rw [haa]
      _ = b := by rw [hu.sq, one_mul]
  have hA : a ∉ Subgroup.zpowers u := by
    intro hmem
    rcases det_tw_eq_one_or_of_mem_zpowers hu.sq hu1 hmem with h1 | h1
    · rw [h1, one_mul] at haa; exact hu1 haa.symm
    · rw [h1, hu.sq] at haa; exact hu1 haa.symm
  have hB : b ∉ Subgroup.zpowers u := by
    intro hmem
    rcases det_tw_eq_one_or_of_mem_zpowers hu.sq hu1 hmem with h1 | h1
    · rw [h1, one_mul] at hbb; exact hu1 hbb.symm
    · rw [h1, hu.sq] at hbb; exact hu1 hbb.symm
  have hAB : a * b ∉ Subgroup.zpowers u := by
    intro hmem
    rcases det_tw_eq_one_or_of_mem_zpowers hu.sq hu1 hmem with h1 | h1
    · rw [h1, one_mul] at hsqab; exact hu1 hsqab.symm
    · rw [h1, hu.sq] at hsqab; exact hu1 hsqab.symm
  have hBA : b⁻¹ * a ∉ Subgroup.zpowers u := by
    intro hmem
    rcases det_tw_eq_one_or_of_mem_zpowers hu.sq hu1 hmem with h1 | h1
    · have hab : a = b := (inv_mul_eq_one.mp h1).symm
      rw [← hab, haa, hu.sq] at hba
      exact hu1 hba
    · have hab : a = b * u := inv_mul_eq_iff_eq_mul.mp h1
      have L : b * (b * u) = 1 := by rw [← mul_assoc, hbb, hu.sq]
      have R : b * u * b = b * (b * u) := by rw [mul_assoc, ← hbu]
      rw [hab, L, R, L, mul_one] at hba
      exact hu1 hba.symm
  have hab_inv_a : (a * b)⁻¹ * a = b⁻¹ := by group
  have hab_inv_b : (a * b)⁻¹ * b = a := inv_mul_eq_iff_eq_mul.mpr hab_a.symm
  have hsame : ∀ (ψ ψ' : G → ZMod 2) (k k' : G), ψ ∈ DE2Hyp.deq2Dual Ω →
      ψ' ∈ DE2Hyp.deq2Dual Ω → ψ u = 0 → ψ' u = 0 →
      (ψ (e 1), ψ (e 2)) = (ψ' (e 1), ψ' (e 2)) → k ∈ K → k' ∈ K →
      IsElationOf Ω u ψ k → IsElationOf Ω u ψ' k' → k'⁻¹ * k ∈ Subgroup.zpowers u := by
    intro ψ ψ' k k' hψ hψ' hψu hψ'u heq hk hk' hel hel'
    have e' := uniq ψ ψ' hψ hψ' hψu hψ'u (congrArg Prod.fst heq) (congrArg Prod.snd heq)
    rw [e'] at hel
    exact dewb2_quot_mem_zpowers h hK hu hk hk' hel hel'
  have hne_a0 : (φa (e 1), φa (e 2)) ≠ (0, 0) := by
    intro heq
    have := hsame φa 0 a 1 hφa hzero hφa0 hzu heq ha K.one_mem hela helz
    rw [inv_one, one_mul] at this
    exact hA this
  have hne_b0 : (φb (e 1), φb (e 2)) ≠ (0, 0) := by
    intro heq
    have := hsame φb 0 b 1 hφb hzero hφb0 hzu heq hb K.one_mem helb helz
    rw [inv_one, one_mul] at this
    exact hB this
  have hne_ab0 : (φab (e 1), φab (e 2)) ≠ (0, 0) := by
    intro heq
    have := hsame φab 0 (a * b) 1 hφab hzero hφab0 hzu heq (K.mul_mem ha hb) K.one_mem
      helab helz
    rw [inv_one, one_mul] at this
    exact hAB this
  have hne_ab : (φa (e 1), φa (e 2)) ≠ (φb (e 1), φb (e 2)) := by
    intro heq
    exact hBA (hsame φa φb a b hφa hφb hφa0 hφb0 heq ha hb hela helb)
  have hne_ab2 : (φa (e 1), φa (e 2)) ≠ (φab (e 1), φab (e 2)) := by
    intro heq
    have := hsame φa φab a (a * b) hφa hφab hφa0 hφab0 heq ha (K.mul_mem ha hb) hela helab
    rw [hab_inv_a] at this
    exact hB (by simpa using (Subgroup.zpowers u).inv_mem this)
  have hne_ab3 : (φb (e 1), φb (e 2)) ≠ (φab (e 1), φab (e 2)) := by
    intro heq
    have := hsame φb φab b (a * b) hφb hφab hφb0 hφab0 heq hb (K.mul_mem ha hb) helb helab
    rw [hab_inv_b] at this
    exact hA this
  rcases dewb2_four (φ (e 1), φ (e 2)) (φa (e 1), φa (e 2)) (φb (e 1), φb (e 2))
      (φab (e 1), φab (e 2)) hne_a0 hne_b0 hne_ab0 hne_ab hne_ab2 hne_ab3 with
    hp | hp | hp | hp
  · have hφ0 : φ = 0 := uniq φ 0 hφ hzero hφu hzu (congrArg Prod.fst hp) (congrArg Prod.snd hp)
    exact ⟨1, K.one_mem, by rw [hφ0]; exact helz⟩
  · have hφa' : φ = φa := uniq φ φa hφ hφa hφu hφa0 (congrArg Prod.fst hp) (congrArg Prod.snd hp)
    exact ⟨a, ha, by rw [hφa']; exact hela⟩
  · have hφb' : φ = φb := uniq φ φb hφ hφb hφu hφb0 (congrArg Prod.fst hp) (congrArg Prod.snd hp)
    exact ⟨b, hb, by rw [hφb']; exact helb⟩
  · have hφab' : φ = φab :=
      uniq φ φab hφ hφab hφu hφab0 (congrArg Prod.fst hp) (congrArg Prod.snd hp)
    exact ⟨a * b, K.mul_mem ha hb, by rw [hφab']; exact helab⟩

private theorem dewb2_partner {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) {k : G}
    (hk : k ∈ K) : ∃ j ∈ J, k * j⁻¹ ∈ pCore 2 G := by
  obtain ⟨φ, hφ, hφu, hel⟩ := h.exists_isElationOf tw.memK tw.invK hk
  obtain ⟨j, hj, hjel⟩ := h.exists_mem_isElationOf tw.memJ tw.invJ hφ hφu
  refine ⟨j, hj, ?_⟩
  have hcent : k * j⁻¹ ∈ Subgroup.centralizer (zGroup Ω : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hy : j⁻¹ * x * j ∈ zGroup Ω := by
      have := h.zGroup_normal.conj_mem x hx j⁻¹
      rwa [inv_inv] at this
    have hjy : j * (j⁻¹ * x * j) * j⁻¹ = x := by group
    have h1 := hjel _ hy
    rw [hjy] at h1
    have h2 := hel _ hy
    have h3 : k * (j⁻¹ * x * j) * k⁻¹ = x := h2.trans h1.symm
    have h4 : (k * j⁻¹) * x * (k * j⁻¹)⁻¹ = x := by
      calc (k * j⁻¹) * x * (k * j⁻¹)⁻¹ = k * (j⁻¹ * x * j) * k⁻¹ := by group
        _ = x := h3
    calc x * (k * j⁻¹) = ((k * j⁻¹) * x * (k * j⁻¹)⁻¹) * (k * j⁻¹) := by rw [h4]
      _ = k * j⁻¹ * x := by group
  rw [h.centralizer_zGroup_eq_pCore] at hcent
  exact hcent

theorem commutes_of_dewTwins {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) :
    Commutes K J :=
  h.commutes_of_mem_twinSet tw.memK ⟨tw.memJ, u, tw.invK, tw.invJ⟩ tw.ne.symm

theorem inf_eq_of_dewTwins {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) :
    K ⊓ J = Subgroup.zpowers u :=
  h.inf_eq_zpowers_of_mem_twinSet tw.memK ⟨tw.memJ, u, tw.invK, tw.invJ⟩ tw.ne.symm tw.invK

theorem card_sup_twins {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) :
    Nat.card ↥(K ⊔ J) = 32 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hc : Commutes K J := h.commutes_of_dewTwins tw
  have huK : u ∈ K := tw.invK.mem
  have huJ : u ∈ J := tw.invJ.mem
  have hu1 : u ≠ 1 := tw.invK.ne_one
  have hcardK : Fintype.card K = 8 := by
    rw [← Nat.card_eq_fintype_card]; exact h.card K tw.memK
  have hcardJ : Fintype.card J = 8 := by
    rw [← Nat.card_eq_fintype_card]; exact h.card J tw.memJ
  have hcard : (Finset.univ : Finset (K × J)).card = 64 := by
    rw [Finset.card_univ, Fintype.card_prod, hcardK, hcardJ]
  let f : K × J → G := fun p => (p.1 : G) * (p.2 : G)
  have hT : (((Finset.univ : Finset (K × J)).image f : Finset G) : Set G) =
      ((K ⊔ J : Subgroup G) : Set G) := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact Subgroup.mul_mem_sup p.1.2 p.2.2
    · intro hx
      obtain ⟨k, hk, j, hj, hkj⟩ := dewb2_mem_sup hc hx
      exact Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨(⟨k, hk⟩, ⟨j, hj⟩), Finset.mem_univ _, hkj⟩)
  have hcardT : Nat.card ↥(K ⊔ J) = ((Finset.univ : Finset (K × J)).image f).card := by
    rw [← Set.ncard_coe_finset, hT]
    exact Nat.card_coe_set_eq _
  have hfib : ∀ b ∈ (Finset.univ : Finset (K × J)).image f,
      ((Finset.univ : Finset (K × J)).filter (fun a => f a = b)).card = 2 := by
    intro b hb
    obtain ⟨⟨⟨k0, hk0⟩, ⟨j0, hj0⟩⟩, -, rfl⟩ := Finset.mem_image.mp hb
    have hk0u : k0 * u ∈ K := K.mul_mem hk0 huK
    have huj0 : u * j0 ∈ J := J.mul_mem huJ hj0
    have hne : ((⟨k0, hk0⟩, ⟨j0, hj0⟩) : K × J) ≠ (⟨k0 * u, hk0u⟩, ⟨u * j0, huj0⟩) := by
      intro heq
      have h1 : k0 = k0 * u := congrArg (fun p : K × J => (p.1 : G)) heq
      have h2 : k0 * 1 = k0 * u := by rw [mul_one]; exact h1
      exact hu1 (mul_left_cancel h2).symm
    have hfilt : (Finset.univ : Finset (K × J)).filter
        (fun a => f a = f (⟨k0, hk0⟩, ⟨j0, hj0⟩))
        = {(⟨k0, hk0⟩, ⟨j0, hj0⟩), (⟨k0 * u, hk0u⟩, ⟨u * j0, huj0⟩)} := by
      ext ⟨⟨k, hk⟩, ⟨j, hj⟩⟩
      simp only [f, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq, Subtype.mk.injEq]
      constructor
      · intro hkj
        have hw : k0⁻¹ * k ∈ K ⊓ J := by
          refine ⟨K.mul_mem (K.inv_mem hk0) hk, ?_⟩
          have e : k0⁻¹ * k = j0 * j⁻¹ := by
            calc k0⁻¹ * k = k0⁻¹ * (k * j) * j⁻¹ := by group
              _ = k0⁻¹ * (k0 * j0) * j⁻¹ := by rw [hkj]
              _ = j0 * j⁻¹ := by group
          rw [e]
          exact J.mul_mem hj0 (J.inv_mem hj)
        rw [h.inf_eq_of_dewTwins tw] at hw
        rcases det_tw_eq_one_or_of_mem_zpowers tw.invK.sq hu1 hw with h1 | h1
        · left
          have hk' : k = k0 := (inv_mul_eq_one.mp h1).symm
          rw [hk'] at hkj
          exact ⟨hk', mul_left_cancel hkj⟩
        · right
          have hk' : k = k0 * u := inv_mul_eq_iff_eq_mul.mp h1
          have hu' : u * j = j0 := by
            have h2 : k0 * (u * j) = k0 * j0 := by
              calc k0 * (u * j) = k0 * u * j := by group
                _ = k * j := by rw [hk']
                _ = k0 * j0 := hkj
            exact mul_left_cancel h2
          refine ⟨hk', ?_⟩
          calc j = u * (u * j) := by rw [← mul_assoc, tw.invK.sq, one_mul]
            _ = u * j0 := by rw [hu']
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · rfl
        · calc k0 * u * (u * j0) = k0 * (u * u) * j0 := by group
            _ = k0 * j0 := by rw [tw.invK.sq, mul_one]
    rw [hfilt, Finset.card_pair hne]
  have h1 := Finset.card_le_mul_card_image (f := f) (Finset.univ : Finset (K × J)) 2
    (fun b hb => (hfib b hb).le)
  have h2 := Finset.mul_card_image_le_card (f := f) (Finset.univ : Finset (K × J)) 2
    (fun b hb => (hfib b hb).ge)
  rw [hcard] at h1 h2
  rw [hcardT]
  omega

private theorem dewb2_sup_pCore_eq {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) :
    K ⊔ pCore 2 G = J ⊔ pCore 2 G := by
  have hle : ∀ {K' J' : Subgroup G}, DewTwins Ω K' J' u → K' ≤ J' ⊔ pCore 2 G := by
    intro K' J' t k hk
    obtain ⟨j, hj, hkj⟩ := dewb2_partner h t hk
    have hm := (J' ⊔ pCore 2 G).mul_mem (Subgroup.mem_sup_right hkj) (Subgroup.mem_sup_left hj)
    rwa [show k * j⁻¹ * j = k by group] at hm
  exact le_antisymm (sup_le (hle tw) le_sup_right) (sup_le (hle tw.symm) le_sup_right)

theorem card_dewDelta {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) :
    Nat.card ↥(dewDelta K J) = 8 := by
  haveI : (pCore 2 G).Normal := pCore_normal
  have hJQ : J ≤ K ⊔ pCore 2 G := by
    rw [dewb2_sup_pCore_eq h tw]
    exact le_sup_left
  have hAQ : (K ⊔ J) ⊔ pCore 2 G = K ⊔ pCore 2 G :=
    le_antisymm (sup_le (sup_le le_sup_left hJQ) le_sup_right)
      (sup_le (le_trans le_sup_left le_sup_left) le_sup_right)
  have hQK : (pCore 2 G).relIndex K = 4 := by
    have h1 := Subgroup.relIndex_mul_card (H := pCore 2 G) (K := K)
    rw [inf_comm, h.inf_pCore tw.memK tw.invK,
      card_zpowers_of_involution tw.invK.sq tw.invK.ne_one, h.card K tw.memK] at h1
    omega
  have hQA : (pCore 2 G).relIndex (K ⊔ J) = 4 := by
    have e1 := Subgroup.relIndex_sup_right (H := K ⊔ J) (K := pCore 2 G)
    have e2 := Subgroup.relIndex_sup_right (H := K) (K := pCore 2 G)
    rw [hAQ] at e1
    rw [← e1, e2, hQK]
  have hA := Subgroup.relIndex_mul_card (H := pCore 2 G) (K := K ⊔ J)
  rw [hQA, inf_comm, h.card_sup_twins tw] at hA
  show Nat.card ↥((K ⊔ J) ⊓ pCore 2 G) = 8
  omega

theorem zpowers_le_dewDelta {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) :
    Subgroup.zpowers u ≤ dewDelta K J := by
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp tw.memK tw.invK
  refine Subgroup.zpowers_le.mpr ?_
  unfold dewDelta
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left tw.invK.mem, h.zGroup_le_pCore huD⟩

private theorem dewb2_dewDelta_decomp {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) {x : G}
    (hx : x ∈ dewDelta K J) : ∃ k ∈ K, ∃ j ∈ J, x = k * j⁻¹ ∧ x ∈ pCore 2 G := by
  unfold dewDelta at hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxs, hxq⟩ := hx
  obtain ⟨k, hk, j, hj, hkj⟩ := dewb2_mem_sup (h.commutes_of_dewTwins tw) hxs
  exact ⟨k, hk, j⁻¹, J.inv_mem hj, by rw [inv_inv, hkj], hxq⟩

theorem dewDelta_mul_self {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) {x : G}
    (hx : x ∈ dewDelta K J) : x * x = 1 := by
  obtain ⟨k, hk, j, hj, rfl, hxQ⟩ := dewb2_dewDelta_decomp h tw hx
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp tw.memK tw.invK
  have huQ : Subgroup.zpowers u ≤ pCore 2 G := Subgroup.zpowers_le.mpr (h.zGroup_le_pCore huD)
  have hc : Commutes K J := h.commutes_of_dewTwins tw
  have hkj_comm : k * j = j * k := hc k hk j hj
  have hjk : j⁻¹ * k = k * j⁻¹ := by
    calc j⁻¹ * k = j⁻¹ * (k * j) * j⁻¹ := by group
      _ = j⁻¹ * (j * k) * j⁻¹ := by rw [hkj_comm]
      _ = k * j⁻¹ := by group
  by_cases hkz : k ∈ Subgroup.zpowers u
  · have hjz : j⁻¹ ∈ Subgroup.zpowers u := by
      have hJQ : j⁻¹ ∈ J ⊓ pCore 2 G := by
        refine Subgroup.mem_inf.mpr ⟨J.inv_mem hj, ?_⟩
        have e : j⁻¹ = k⁻¹ * (k * j⁻¹) := by group
        rw [e]
        exact (pCore 2 G).mul_mem ((pCore 2 G).inv_mem (huQ hkz)) hxQ
      rw [h.inf_pCore tw.memJ tw.invJ] at hJQ
      exact hJQ
    have hxz : k * j⁻¹ ∈ Subgroup.zpowers u := (Subgroup.zpowers u).mul_mem hkz hjz
    rcases det_tw_eq_one_or_of_mem_zpowers tw.invK.sq tw.invK.ne_one hxz with h1 | h1
    · rw [h1, mul_one]
    · rw [h1, tw.invK.sq]
  · obtain ⟨i, i', hi, hi', hii, hi'i', hi'i, hNF⟩ :=
      exists_q8_gen tw.invK (h.isQuatSub_of_mem tw.memK) (h.card K tw.memK)
    have hQK : Q8Data K u i i' := ⟨tw.invK, hi, hi', hii, hi'i', hi'i, hNF⟩
    have hkk : k * k = u := det_tw_q8_sq hQK hk hkz
    have hjz : j ∉ Subgroup.zpowers u := by
      intro hjz
      apply hkz
      have hkQ : k ∈ K ⊓ pCore 2 G := by
        refine Subgroup.mem_inf.mpr ⟨hk, ?_⟩
        have e : k = (k * j⁻¹) * j := by group
        rw [e]
        exact (pCore 2 G).mul_mem hxQ (huQ hjz)
      rw [h.inf_pCore tw.memK tw.invK] at hkQ
      exact hkQ
    obtain ⟨c, d, hc', hd', hcc, hdd, hdc, hNF'⟩ :=
      exists_q8_gen tw.invJ (h.isQuatSub_of_mem tw.memJ) (h.card J tw.memJ)
    have hQJ : Q8Data J u c d := ⟨tw.invJ, hc', hd', hcc, hdd, hdc, hNF'⟩
    have hjj : j * j = u := det_tw_q8_sq hQJ hj hjz
    have hjinv : j⁻¹ * j⁻¹ = u := by
      rw [← mul_inv_rev, hjj]
      exact inv_eq_of_mul_eq_one_right tw.invK.sq
    calc k * j⁻¹ * (k * j⁻¹) = k * (j⁻¹ * k) * j⁻¹ := by group
      _ = k * (k * j⁻¹) * j⁻¹ := by rw [hjk]
      _ = (k * k) * (j⁻¹ * j⁻¹) := by group
      _ = u * u := by rw [hkk, hjinv]
      _ = 1 := tw.invK.sq

theorem dewDelta_comm {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) {x y : G}
    (hx : x ∈ dewDelta K J) (hy : y ∈ dewDelta K J) : x * y = y * x := by
  have hxy : x * y ∈ dewDelta K J := (dewDelta K J).mul_mem hx hy
  have h1 := h.dewDelta_mul_self tw hx
  have h2 := h.dewDelta_mul_self tw hy
  have h3 := h.dewDelta_mul_self tw hxy
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h3).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [inv_eq_of_mul_eq_one_right h1, inv_eq_of_mul_eq_one_right h2]

theorem exists_partner {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) {k : G} (hk : k ∈ K) :
    ∃ j ∈ J, k * j⁻¹ ∈ pCore 2 G :=
  dewb2_partner h tw hk

theorem mem_dewDelta_iff {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) {x : G} :
    x ∈ dewDelta K J ↔ ∃ k ∈ K, ∃ j ∈ J, x = k * j⁻¹ ∧ x ∈ pCore 2 G := by
  constructor
  · intro hx
    exact dewb2_dewDelta_decomp h tw hx
  · rintro ⟨k, hk, j, hj, rfl, hq⟩
    unfold dewDelta
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem_sup hk (J.inv_mem hj), hq⟩

theorem dewDelta_act_of_commute {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u) {k j v : G}
    (hk : k ∈ K) (hj : j ∈ J) (hkj : k * j⁻¹ ∈ pCore 2 G) (hv : v ∈ zGroup Ω)
    (hkv : k * v = v * k) {M : Subgroup G} (hM : M ∈ dew1V Ω v) :
    conjSub (k * j⁻¹) M = M := by
  obtain ⟨hMΩ, hMv⟩ := hM
  have hC : k * j⁻¹ ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
    h.pCore_le_centralizer_zGroup hkj
  have hcv : k * j⁻¹ * v = v * (k * j⁻¹) := (Subgroup.mem_centralizer_iff.mp hC v hv).symm
  have hmem : k * j⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
    by_cases hvu : v = u
    · have hM' : M ∈ dew1V Ω u := ⟨hMΩ, hvu ▸ hMv⟩
      exact (Subgroup.normalizer (M : Set G)).mul_mem
        (h.le_normalizer_of_dew1V tw.memK tw.invK hM' hk)
        ((Subgroup.normalizer (M : Set G)).inv_mem
          (h.le_normalizer_of_dew1V tw.memJ tw.invJ hM' hj))
    · have hv1 : v ≠ 1 := hMv.ne_one
      have hvz : v ∉ Subgroup.zpowers u := by
        intro hz
        rcases det_tw_eq_one_or_of_mem_zpowers tw.invK.sq tw.invK.ne_one hz with h1 | h1
        · exact hv1 h1
        · exact hvu h1
      have hkN : k ∈ Subgroup.normalizer (M : Set G) :=
        h.inf_centralizer_le_normalizer tw.memK tw.invK hv hvz (Or.inl ⟨hMΩ, hMv⟩)
          (Subgroup.mem_inf.mpr ⟨hk, Subgroup.mem_centralizer_singleton_iff.mpr hkv⟩)
      have hkinv : k⁻¹ * v = v * k⁻¹ := by
        calc k⁻¹ * v = k⁻¹ * (v * k) * k⁻¹ := by group
          _ = k⁻¹ * (k * v) * k⁻¹ := by rw [hkv]
          _ = v * k⁻¹ := by group
      have hj' : j⁻¹ * v = v * j⁻¹ := by
        calc j⁻¹ * v = k⁻¹ * ((k * j⁻¹) * v) := by group
          _ = k⁻¹ * (v * (k * j⁻¹)) := by rw [hcv]
          _ = (k⁻¹ * v) * (k * j⁻¹) := by group
          _ = (v * k⁻¹) * (k * j⁻¹) := by rw [hkinv]
          _ = v * j⁻¹ := by group
      have hjv : j * v = v * j := by
        calc j * v = j * (v * j⁻¹) * j := by group
          _ = j * (j⁻¹ * v) * j := by rw [hj']
          _ = v * j := by group
      have hjN : j ∈ Subgroup.normalizer (M : Set G) :=
        h.inf_centralizer_le_normalizer tw.memJ tw.invJ hv hvz (Or.inl ⟨hMΩ, hMv⟩)
          (Subgroup.mem_inf.mpr ⟨hj, Subgroup.mem_centralizer_singleton_iff.mpr hjv⟩)
      exact (Subgroup.normalizer (M : Set G)).mul_mem hkN
        ((Subgroup.normalizer (M : Set G)).inv_mem hjN)
  exact mem_normalizer_iff_conjSub_eq.mp hmem

theorem dewDelta_act_of_not_commute {K J : Subgroup G} {u : G} (tw : DewTwins Ω K J u)
    {k j v : G} (hk : k ∈ K) (hj : j ∈ J) (hkj : k * j⁻¹ ∈ pCore 2 G) (hv : v ∈ zGroup Ω)
    (hkv : k * v ≠ v * k) {M : Subgroup G} (hM : M ∈ dew1V Ω v) :
    conjSub (k * j⁻¹) M = dewTau K J M := by
  obtain ⟨hMΩ, hMv⟩ := hM
  have huD : u ∈ zGroup Ω := dew1_involution_mem h.toDEHyp tw.memK tw.invK
  have hC : k * j⁻¹ ∈ Subgroup.centralizer (zGroup Ω : Set G) :=
    h.pCore_le_centralizer_zGroup hkj
  have hc : Commutes K J := h.commutes_of_dewTwins tw
  have hkj_comm : k * j = j * k := hc k hk j hj
  have hjk : j⁻¹ * k = k * j⁻¹ := by
    calc j⁻¹ * k = j⁻¹ * (k * j) * j⁻¹ := by group
      _ = j⁻¹ * (j * k) * j⁻¹ := by rw [hkj_comm]
      _ = k * j⁻¹ := by group
  have hku : k * u = u * k := mul_inv_eq_iff_eq_mul.mp (conj_of_mem_mem tw.invK hk (Or.inr rfl))
  have hne_uv : u ≠ v := by
    intro huv
    apply hkv
    rw [← huv]
    exact hku
  have sp1 : DewPair Ω K M u v := ⟨tw.memK, hMΩ, tw.invK, hMv, hne_uv⟩
  obtain ⟨hNΩ, hNu⟩ := h.dewStar_mem_dew1V sp1
  have hv1 : v ≠ 1 := hMv.ne_one
  have sp2 : DewPair Ω J (dewStar K M) u (u * v) :=
    ⟨tw.memJ, hNΩ, tw.invJ, hNu, dewb2_ne_mul hv1⟩
  have hjv : j⁻¹ * (u * v) ≠ u * v * j⁻¹ := by
    intro heq
    have hw : u * v ∈ zGroup Ω := (zGroup Ω).mul_mem huD hv
    have hcw : k * j⁻¹ * (u * v) = u * v * (k * j⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hC (u * v) hw).symm
    have hkw : k * (u * v) = u * v * k := by
      have e1 : k * j⁻¹ * (u * v) = (k * (u * v)) * j⁻¹ := by
        calc k * j⁻¹ * (u * v) = k * (j⁻¹ * (u * v)) := by group
          _ = k * (u * v * j⁻¹) := by rw [heq]
          _ = (k * (u * v)) * j⁻¹ := by group
      have e2 : u * v * (k * j⁻¹) = (u * v * k) * j⁻¹ := by group
      rw [e1, e2] at hcw
      exact mul_right_cancel hcw
    apply hkv
    have e3 : u * (k * v) = u * (v * k) := by
      calc u * (k * v) = (u * k) * v := by group
        _ = (k * u) * v := by rw [hku]
        _ = k * (u * v) := by group
        _ = u * v * k := hkw
        _ = u * (v * k) := by group
    exact mul_left_cancel e3
  calc conjSub (k * j⁻¹) M = conjSub j⁻¹ (conjSub k M) := by rw [← hjk, conjSub_mul]
    _ = conjSub j⁻¹ (dewStar K M) := by rw [← h.dewStar_eq sp1 hk hkv]
    _ = dewStar J (dewStar K M) := (h.dewStar_eq sp2 (J.inv_mem hj) hjv).symm
    _ = dewTau K J M := rfl

theorem dewTau_mem {K J : Subgroup G} {u v : G} (hK : K ∈ dew1V Ω u) (hJ : J ∈ dew1V Ω u)
    (hvu : v ≠ u) {M : Subgroup G} (hM : M ∈ dew1V Ω v) : dewTau K J M ∈ dew1V Ω v := by
  obtain ⟨hKΩ, hKu⟩ := hK
  obtain ⟨hJΩ, hJu⟩ := hJ
  obtain ⟨hMΩ, hMv⟩ := hM
  have hv1 : v ≠ 1 := hMv.ne_one
  have sp1 : DewPair Ω K M u v := ⟨hKΩ, hMΩ, hKu, hMv, fun h' => hvu h'.symm⟩
  obtain ⟨hNΩ, hNu⟩ := h.dewStar_mem_dew1V sp1
  have sp2 : DewPair Ω J (dewStar K M) u (u * v) :=
    ⟨hJΩ, hNΩ, hJu, hNu, dewb2_ne_mul hv1⟩
  have hR : dewStar J (dewStar K M) ∈ dew1V Ω (u * (u * v)) := h.dewStar_mem_dew1V sp2
  rw [← mul_assoc, hKu.sq, one_mul] at hR
  exact hR

theorem dewTau_dewTau {K J : Subgroup G} {u v : G} (hK : K ∈ dew1V Ω u) (hJ : J ∈ dew1V Ω u)
    (hvu : v ≠ u) {M : Subgroup G} (hM : M ∈ dew1V Ω v) :
    dewTau K J (dewTau K J M) = M := by
  obtain ⟨hKΩ, hKu⟩ := hK
  obtain ⟨hJΩ, hJu⟩ := hJ
  obtain ⟨hMΩ, hMv⟩ := hM
  have hvD : v ∈ zGroup Ω := dew1_involution_mem h.toDEHyp hMΩ hMv
  have hne : u ≠ v := fun h' => hvu h'.symm
  by_cases hKJ : K = J
  · subst hKJ
    have sp : DewPair Ω K M u v := ⟨hKΩ, hMΩ, hKu, hMv, hne⟩
    have h1 : dewTau K K M = M := h.dewStar_dewStar sp
    rw [h1, h1]
  · have tw : DewTwins Ω K J u := ⟨hKΩ, hJΩ, hKu, hJu, hKJ⟩
    obtain ⟨k, hk, hkv⟩ := h.exists_not_comm_of_dewPair ⟨hKΩ, hMΩ, hKu, hMv, hne⟩
    obtain ⟨j, hj, hkj⟩ := h.exists_partner tw hk
    have hδ : k * j⁻¹ ∈ dewDelta K J := (h.mem_dewDelta_iff tw).mpr ⟨k, hk, j, hj, rfl, hkj⟩
    have hsq : k * j⁻¹ * (k * j⁻¹) = 1 := h.dewDelta_mul_self tw hδ
    have hact : ∀ X : Subgroup G, X ∈ dew1V Ω v → conjSub (k * j⁻¹) X = dewTau K J X :=
      fun X hX => h.dewDelta_act_of_not_commute tw hk hj hkj hvD hkv hX
    have hK' : K ∈ dew1V Ω u := ⟨hKΩ, hKu⟩
    have hJ' : J ∈ dew1V Ω u := ⟨hJΩ, hJu⟩
    have hM' : M ∈ dew1V Ω v := ⟨hMΩ, hMv⟩
    have hτM : dewTau K J M ∈ dew1V Ω v := h.dewTau_mem hK' hJ' hvu hM'
    rw [← hact (dewTau K J M) hτM, ← hact M hM', ← conjSub_mul, hsq, conjSub_one]

theorem dewTau_comp {K₁ K₂ K₃ : Subgroup G} {u v : G} (h₁ : K₁ ∈ dew1V Ω u)
    (h₂ : K₂ ∈ dew1V Ω u) (h₃ : K₃ ∈ dew1V Ω u) (hvu : v ≠ u) {M : Subgroup G}
    (hM : M ∈ dew1V Ω v) : dewTau K₂ K₃ (dewTau K₁ K₂ M) = dewTau K₁ K₃ M := by
  obtain ⟨h₁Ω, h₁u⟩ := h₁
  obtain ⟨h₂Ω, h₂u⟩ := h₂
  obtain ⟨hMΩ, hMv⟩ := hM
  have hv1 : v ≠ 1 := hMv.ne_one
  have sp1 : DewPair Ω K₁ M u v := ⟨h₁Ω, hMΩ, h₁u, hMv, fun h' => hvu h'.symm⟩
  obtain ⟨hNΩ, hNu⟩ := h.dewStar_mem_dew1V sp1
  have sp2 : DewPair Ω K₂ (dewStar K₁ M) u (u * v) :=
    ⟨h₂Ω, hNΩ, h₂u, hNu, dewb2_ne_mul hv1⟩
  show dewStar K₃ (dewStar K₂ (dewStar K₂ (dewStar K₁ M))) = dewStar K₃ (dewStar K₁ M)
  rw [h.dewStar_dewStar sp2]

theorem mem_dewKer_iff {u g : G} :
    g ∈ dewKer Ω u ↔ g ∈ Subgroup.centralizer ({u} : Set G) ∧
      ∀ M ∈ dew1V Ω u, conjSub g M = M := by
  simp only [dewKer, Subgroup.mem_inf, Subgroup.mem_iInf, mem_normalizer_iff_conjSub_eq]

theorem inf_centralizer_le_dewKer {M : Subgroup G} {c u : G} (hM : M ∈ Ω)
    (hc : IsUniqueInvolution M c) (hu : u ∈ zGroup Ω) (huc : u ∉ Subgroup.zpowers c) :
    M ⊓ Subgroup.centralizer ({u} : Set G) ≤ dewKer Ω u := by
  obtain ⟨-, -, hn⟩ := h.det_tw_core hM hc hu huc
  intro x hx
  refine (h.mem_dewKer_iff).mpr ⟨hx.2, fun J hJ => ?_⟩
  have hJM : J ≠ M := by
    rintro rfl
    apply huc
    have hcu : c = u := hc.eq hJ.2
    rw [← hcu]
    exact Subgroup.mem_zpowers c
  exact mem_normalizer_iff_conjSub_eq.mp (hn J hJ.1 hJM hJ.2 hx)

omit h in
theorem dewb3_tau_zero : det_tw_tau (0 : Fin 3 → ZMod 2) = 1 :=
  TL4.matrix_ext_mulVec fun w => by
    rw [det_tw_tau_mulVec, Matrix.one_mulVec]
    simp

omit h in
theorem dewb3_tau_e0 : det_tw_tau ![1, 0, 0] = 1 :=
  TL4.matrix_ext_mulVec fun w => by
    rw [det_tw_tau_mulVec, Matrix.one_mulVec]
    simp

theorem dewb3_exists_tau {u : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1)
    {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) (he0 : e 0 = u)
    {v : Fin 3 → ZMod 2} (hv0 : v ≠ 0) (hv1 : v ≠ ![1, 0, 0]) :
    ∃ n ∈ dewKer Ω u, TL4.conjMat he n = det_tw_tau v := by
  have hv' : v 1 ≠ 0 ∨ v 2 ≠ 0 := by
    have key : ∀ w : Fin 3 → ZMod 2, w ≠ 0 → w ≠ ![1, 0, 0] → w 1 ≠ 0 ∨ w 2 ≠ 0 := by
      decide
    exact key v hv0 hv1
  have hcD : TL4.e8Coord e v ∈ zGroup Ω := TL4.e8Coord_mem he v
  have hc1 : TL4.e8Coord e v ≠ 1 := by
    intro h1
    apply hv0
    apply TL4.e8Coord_injective he
    rw [h1, TL4.e8Coord_zero]
  have hE0 : TL4.e8Coord e ![1, 0, 0] = u := by
    rw [show (![1, 0, 0] : Fin 3 → ZMod 2) = Pi.single 0 1 from by
      funext k; fin_cases k <;> simp, TL4.e8Coord_single, he0]
  have hcu : TL4.e8Coord e v ≠ u := by
    intro h1
    apply hv1
    apply TL4.e8Coord_injective he
    rw [hE0, h1]
  obtain ⟨M, hM, hMc⟩ : ∃ M ∈ Ω, IsUniqueInvolution M (TL4.e8Coord e v) := by
    rcases (h.mem_zGroup_iff).mp hcD with h1 | h1
    · exact absurd h1 hc1
    · exact h1
  have huc : u ∉ Subgroup.zpowers (TL4.e8Coord e v) := by
    intro hmem
    rcases det_tw_eq_one_or_of_mem_zpowers hMc.sq hMc.ne_one hmem with h1 | h1
    · exact hu1 h1
    · exact hcu h1.symm
  obtain ⟨hU4, -, -⟩ := h.det_tw_core hM hMc hu huc
  have hnot : ¬ (M ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.zpowers (TL4.e8Coord e v)) :=
    fun hle => by
      have hc := Subgroup.card_le_of_le hle
      rw [hU4, card_zpowers_of_involution hMc.sq hc1] at hc
      omega
  obtain ⟨x, hxU, hxc⟩ : ∃ x ∈ M ⊓ Subgroup.centralizer ({u} : Set G),
      x ∉ Subgroup.zpowers (TL4.e8Coord e v) := by
    by_contra hcon
    push_neg at hcon
    exact hnot hcon
  have hxu : x * u = u * x := Subgroup.mem_centralizer_singleton_iff.mp hxU.2
  refine ⟨x, h.inf_centralizer_le_dewKer hM hMc hu huc hxU, ?_⟩
  exact h.det_tw_conjMat_formula hM hMc he rfl hv' hxU.1 (by rw [he0]; exact hxu) hxc

theorem dewb3_stab {u : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1)
    {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) (he0 : e 0 = u) :
    ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det ≠ 0 → A.mulVec ![1, 0, 0] = ![1, 0, 0] →
      ∃ n ∈ dewKer Ω u, TL4.conjMat he n = A := by
  have hxN : ∀ g : G, ∀ y ∈ zGroup Ω, g * y * g⁻¹ ∈ zGroup Ω :=
    fun g y hy => h.zGroup_normal.conj_mem y hy g
  have htau : ∀ a : Fin 3 → ZMod 2, ∃ n ∈ dewKer Ω u, TL4.conjMat he n = det_tw_tau a := by
    intro a
    by_cases ha0 : a = 0
    · subst ha0
      exact ⟨1, one_mem _, (TL4.conjMat_one he).trans dewb3_tau_zero.symm⟩
    by_cases ha1 : a = ![1, 0, 0]
    · subst ha1
      exact ⟨1, one_mem _, (TL4.conjMat_one he).trans dewb3_tau_e0.symm⟩
    exact h.dewb3_exists_tau hu hu1 he he0 ha0 ha1
  intro A hA hA0
  obtain ⟨a, b, c, rfl⟩ := det_tw_finite A hA hA0
  obtain ⟨na, hna, hna'⟩ := htau a
  obtain ⟨nb, hnb, hnb'⟩ := htau b
  obtain ⟨nc, hnc, hnc'⟩ := htau c
  refine ⟨na * nb * nc, mul_mem (mul_mem hna hnb) hnc, ?_⟩
  rw [TL4.conjMat_mul he (hxN _) (hxN _), TL4.conjMat_mul he (hxN _) (hxN _), hna', hnb', hnc']

theorem centralizer_eq_dewKer_sup {u : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) :
    Subgroup.centralizer ({u} : Set G) = dewKer Ω u ⊔ pCore 2 G := by
  obtain ⟨e, he, he0⟩ := h.det_tw_basis hu hu1
  have hE0 : TL4.e8Coord e ![1, 0, 0] = u := by
    rw [show (![1, 0, 0] : Fin 3 → ZMod 2) = Pi.single 0 1 from by
      funext k; fin_cases k <;> simp, TL4.e8Coord_single, he0]
  have hxN : ∀ g : G, ∀ y ∈ zGroup Ω, g * y * g⁻¹ ∈ zGroup Ω :=
    fun g y hy => h.zGroup_normal.conj_mem y hy g
  have hstab := h.dewb3_stab hu hu1 he he0
  apply le_antisymm
  · intro g hg
    have hgu : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgu' : g * u * g⁻¹ = u := by rw [hgu]; group
    have hfix : (TL4.conjMat he g).mulVec ![1, 0, 0] = ![1, 0, 0] := by
      apply TL4.e8Coord_injective he
      rw [← TL4.conj_e8Coord he (hxN g) ![1, 0, 0], hE0, hgu']
    have hdet : (TL4.conjMat he g).det ≠ 0 := by
      rw [TL4.det_conjMat he (hxN g) (fun z hz => h.zGroup_normal.conj_mem z hz g⁻¹)]
      exact one_ne_zero
    obtain ⟨n, hn, hnr⟩ := hstab _ hdet hfix
    have hker : n⁻¹ * g ∈ (h.rhoD he).ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show TL4.conjMat he (n⁻¹ * g) = 1
      have hnn : TL4.conjMat he n⁻¹ * TL4.conjMat he n = 1 := by
        rw [← TL4.conjMat_mul he (hxN n⁻¹) (hxN n), inv_mul_cancel, TL4.conjMat_one he]
      rw [TL4.conjMat_mul he (hxN n⁻¹) (hxN g), ← hnr, hnn]
    rw [h.rhoD_ker he, h.centralizer_zGroup_eq_pCore] at hker
    have hg' : g = n * (n⁻¹ * g) := by group
    rw [hg']
    exact mul_mem (Subgroup.mem_sup_left hn) (Subgroup.mem_sup_right hker)
  · refine sup_le (fun x hx => ?_) (fun g hg => ?_)
    · exact ((h.mem_dewKer_iff).mp hx).1
    · rw [← h.centralizer_zGroup_eq_pCore] at hg
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hg) u hu).symm

omit h in
theorem dewb3_zmod_two_det : ∀ d : ZMod 2, d ≠ 0 → d = 1 := by decide

omit h in
theorem dewb3_fin_two_fixed : ∀ a b : Fin 3 → ZMod 2, a ≠ 0 → b ≠ 0 → a ≠ b →
    ∃ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det ≠ 0 ∧ A.mulVec a = ![1, 0, 0] ∧
      A.mulVec b = ![0, 1, 0] := by
  decide +kernel

omit h in
theorem dewb3_fin_cube : ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 → u ≠ v →
    ∃ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det ≠ 0 ∧ A ^ 3 = 1 ∧ A.mulVec u = v ∧
      A.mulVec v = u + v := by
  decide +kernel

omit h in
def dewb3_A7 : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

omit h in
theorem dewb3_A7_order : dewb3_A7 ^ 7 = 1 ∧ dewb3_A7 ≠ 1 ∧ dewb3_A7.det ≠ 0 := by
  decide +kernel

omit h in
theorem dewb3_fin_regular : ∀ a b : Fin 3 → ZMod 2, a ≠ 0 → b ≠ 0 →
    ∃ i : Fin 7, (dewb3_A7 ^ (i : ℕ)).mulVec a = b := by
  decide +kernel

set_option synthInstance.maxSize 1024 in
omit h in
theorem dewb3_fin_lines : ∀ a b a' b' : Fin 3 → ZMod 2, a ≠ 0 → b ≠ 0 → a ≠ b →
    a' ≠ 0 → b' ≠ 0 → a' ≠ b' →
    ∃ i : Fin 7, ({(dewb3_A7 ^ (i : ℕ)).mulVec a, (dewb3_A7 ^ (i : ℕ)).mulVec b,
      (dewb3_A7 ^ (i : ℕ)).mulVec (a + b)} : Finset (Fin 3 → ZMod 2)) = {a', b', a' + b'} := by
  decide +kernel

theorem dewb3_exists_conjMat {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e)
    {A : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hA : A.det ≠ 0) :
    ∃ g : G, TL4.conjMat he g = A := by
  have hmem' : ∀ B : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), B ∈ (h.rhoD he).range := by
    intro B
    rw [h.rhoD_range he]
    exact Subgroup.mem_top _
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (hmem' ⟨A, dewb3_zmod_two_det _ hA⟩)
  exact ⟨g, congrArg Subtype.val hg⟩

theorem dewb3_conjMat_pow {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) (g : G) (i : ℕ) :
    TL4.conjMat he (g ^ i) = TL4.conjMat he g ^ i := by
  have h1 := congrArg Subtype.val (map_pow (h.rhoD he) g i)
  exact h1.trans (Matrix.SpecialLinearGroup.coe_pow _ _)

theorem dewb3_lift {e : Fin 3 → G} (he : TL4.E8Basis (zGroup Ω) e) {g : G} {n : ℕ}
    (hn : Odd n) (hn1 : 1 < n) (hgn : TL4.conjMat he g ^ n = 1) :
    ∃ y : G, y ^ n = 1 ∧ TL4.conjMat he y = TL4.conjMat he g := by
  have hρn : h.rhoD he g ^ n = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    exact hgn
  have hmem : g ^ n ∈ pCore 2 G := by
    rw [← h.centralizer_zGroup_eq_pCore, ← h.rhoD_ker he, MonoidHom.mem_ker, map_pow, hρn]
  obtain ⟨j, hj⟩ := (CFSG.pCore_isPGroup (p := 2) (G := G)) ⟨g ^ n, hmem⟩
  have hj' : (g ^ n) ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have hcop : Nat.Coprime (2 ^ j) n := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hn)
  have hkm : 2 ^ j ∣ (2 ^ j) ^ Nat.totient n :=
    dvd_pow_self _ (Nat.totient_pos.mpr (by omega)).ne'
  have hk1 : (2 ^ j) ^ Nat.totient n % n = 1 := by
    have := Nat.ModEq.pow_totient hcop
    rw [Nat.ModEq, Nat.mod_eq_of_lt hn1] at this
    exact this
  refine ⟨g ^ ((2 ^ j) ^ Nat.totient n), ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul]
    obtain ⟨t, ht⟩ := hkm
    rw [ht, pow_mul, hj', one_pow]
  · have hpow : h.rhoD he (g ^ ((2 ^ j) ^ Nat.totient n)) = h.rhoD he g := by
      rw [map_pow, pow_eq_pow_mod ((2 ^ j) ^ Nat.totient n) hρn, hk1, pow_one]
    exact congrArg Subtype.val hpow

theorem exists_conj_pair {y x y' x' : G} (hy : y ∈ zGroup Ω) (hx : x ∈ zGroup Ω)
    (hy' : y' ∈ zGroup Ω) (hx' : x' ∈ zGroup Ω) (hy1 : y ≠ 1) (hx1 : x ≠ 1) (hy'1 : y' ≠ 1)
    (hx'1 : x' ≠ 1) (hyx : y ≠ x) (hyx' : y' ≠ x') :
    ∃ g : G, g * y * g⁻¹ = y' ∧ g * x * g⁻¹ = x' := by
  obtain ⟨e, he⟩ := h.exists_basis
  obtain ⟨a, rfl⟩ := TL4.exists_e8Coord_eq he hy
  obtain ⟨b, rfl⟩ := TL4.exists_e8Coord_eq he hx
  obtain ⟨a', rfl⟩ := TL4.exists_e8Coord_eq he hy'
  obtain ⟨b', rfl⟩ := TL4.exists_e8Coord_eq he hx'
  have ha0 : a ≠ 0 := fun h0 => hy1 (by rw [h0, TL4.e8Coord_zero])
  have hb0 : b ≠ 0 := fun h0 => hx1 (by rw [h0, TL4.e8Coord_zero])
  have ha0' : a' ≠ 0 := fun h0 => hy'1 (by rw [h0, TL4.e8Coord_zero])
  have hb0' : b' ≠ 0 := fun h0 => hx'1 (by rw [h0, TL4.e8Coord_zero])
  have hab : a ≠ b := fun h0 => hyx (by rw [h0])
  have hab' : a' ≠ b' := fun h0 => hyx' (by rw [h0])
  obtain ⟨A, hA, hAa, hAb⟩ := dewb3_fin_two_fixed a b ha0 hb0 hab
  obtain ⟨B, hB, hBa, hBb⟩ := dewb3_fin_two_fixed a' b' ha0' hb0' hab'
  obtain ⟨gA, hgA⟩ := h.dewb3_exists_conjMat he hA
  obtain ⟨gB, hgB⟩ := h.dewb3_exists_conjMat he hB
  have hxN : ∀ g : G, ∀ z ∈ zGroup Ω, g * z * g⁻¹ ∈ zGroup Ω :=
    fun g z hz => h.zGroup_normal.conj_mem z hz g
  have hA_y : gA * TL4.e8Coord e a * gA⁻¹ = TL4.e8Coord e ![1, 0, 0] := by
    rw [TL4.conj_e8Coord he (hxN gA) a, hgA, hAa]
  have hA_x : gA * TL4.e8Coord e b * gA⁻¹ = TL4.e8Coord e ![0, 1, 0] := by
    rw [TL4.conj_e8Coord he (hxN gA) b, hgA, hAb]
  have hB_y : gB * TL4.e8Coord e a' * gB⁻¹ = TL4.e8Coord e ![1, 0, 0] := by
    rw [TL4.conj_e8Coord he (hxN gB) a', hgB, hBa]
  have hB_x : gB * TL4.e8Coord e b' * gB⁻¹ = TL4.e8Coord e ![0, 1, 0] := by
    rw [TL4.conj_e8Coord he (hxN gB) b', hgB, hBb]
  refine ⟨gB⁻¹ * gA, ?_, ?_⟩
  · calc gB⁻¹ * gA * TL4.e8Coord e a * (gB⁻¹ * gA)⁻¹
        = gB⁻¹ * (gA * TL4.e8Coord e a * gA⁻¹) * gB := by group
      _ = gB⁻¹ * (gB * TL4.e8Coord e a' * gB⁻¹) * gB := by rw [hA_y, hB_y]
      _ = TL4.e8Coord e a' := by group
  · calc gB⁻¹ * gA * TL4.e8Coord e b * (gB⁻¹ * gA)⁻¹
        = gB⁻¹ * (gA * TL4.e8Coord e b * gA⁻¹) * gB := by group
      _ = gB⁻¹ * (gB * TL4.e8Coord e b' * gB⁻¹) * gB := by rw [hA_x, hB_x]
      _ = TL4.e8Coord e b' := by group

theorem exists_kernel_conj {u v v' : G} (hu : u ∈ zGroup Ω) (hu1 : u ≠ 1) (hv : v ∈ zGroup Ω)
    (hv' : v' ∈ zGroup Ω) (hvu : v ∉ Subgroup.zpowers u) (hv'u : v' ∉ Subgroup.zpowers u) :
    ∃ w ∈ dewKer Ω u, w * v * w⁻¹ = v' := by
  have hne : ∀ {a : G}, a ∉ Subgroup.zpowers u → a ≠ 1 ∧ u ≠ a := by
    intro a ha
    exact ⟨fun h1 => ha (h1 ▸ Subgroup.one_mem _), fun h1 => ha (h1 ▸ Subgroup.mem_zpowers _)⟩
  obtain ⟨hv1, huv⟩ := hne hvu
  obtain ⟨hv'1, huv'⟩ := hne hv'u
  obtain ⟨g, hg1, hg2⟩ := h.exists_conj_pair hu hv hu hv' hu1 hv1 hu1 hv'1 huv huv'
  have hgC : g ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * u = (g * u * g⁻¹) * g := by group
      _ = u * g := by rw [hg1]
  rw [h.centralizer_eq_dewKer_sup hu hu1] at hgC
  haveI : (pCore 2 G).Normal := CFSG.pCore_normal
  obtain ⟨w, hw, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hgC
  refine ⟨w, hw, ?_⟩
  have hqv : q * v * q⁻¹ = v := by
    have := Subgroup.mem_centralizer_iff.mp (h.pCore_le_centralizer_zGroup hq) v hv
    rw [← this]
    group
  rw [← hg2]
  calc w * v * w⁻¹ = w * (q * v * q⁻¹) * w⁻¹ := by rw [hqv]
    _ = w * q * v * (w * q)⁻¹ := by group

theorem exists_cube {u v : G} (hu : u ∈ zGroup Ω) (hv : v ∈ zGroup Ω) (hu1 : u ≠ 1)
    (hv1 : v ≠ 1) (huv : u ≠ v) :
    ∃ y : G, y ^ 3 = 1 ∧ y * u * y⁻¹ = v ∧ y * v * y⁻¹ = u * v := by
  obtain ⟨e, he⟩ := h.exists_basis
  obtain ⟨a, rfl⟩ := TL4.exists_e8Coord_eq he hu
  obtain ⟨b, rfl⟩ := TL4.exists_e8Coord_eq he hv
  have ha0 : a ≠ 0 := fun h0 => hu1 (by rw [h0, TL4.e8Coord_zero])
  have hb0 : b ≠ 0 := fun h0 => hv1 (by rw [h0, TL4.e8Coord_zero])
  have hab : a ≠ b := fun h0 => huv (by rw [h0])
  obtain ⟨A, hA, hA3, hAa, hAb⟩ := dewb3_fin_cube a b ha0 hb0 hab
  obtain ⟨g, hg⟩ := h.dewb3_exists_conjMat he hA
  have hxN : ∀ g : G, ∀ z ∈ zGroup Ω, g * z * g⁻¹ ∈ zGroup Ω :=
    fun g z hz => h.zGroup_normal.conj_mem z hz g
  obtain ⟨y, hy3, hyg⟩ := h.dewb3_lift he (n := 3) ⟨1, rfl⟩ (by norm_num) (by rw [hg, hA3])
  refine ⟨y, hy3, ?_, ?_⟩
  · rw [TL4.conj_e8Coord he (hxN y) a, hyg, hg, hAa]
  · rw [TL4.conj_e8Coord he (hxN y) b, hyg, hg, hAb, TL4.e8Coord_add he]

theorem exists_order_seven : ∃ g : G, orderOf g = 7 ∧
    (∀ x ∈ zGroup Ω, x ≠ 1 → ∀ y ∈ zGroup Ω, y ≠ 1 → ∃ i : ℕ, g ^ i * x * (g ^ i)⁻¹ = y) ∧
    (∀ u ∈ zGroup Ω, ∀ v ∈ zGroup Ω, u ≠ 1 → v ≠ 1 → u ≠ v → ∀ u' ∈ zGroup Ω, ∀ v' ∈ zGroup Ω,
      u' ≠ 1 → v' ≠ 1 → u' ≠ v' → ∃ i : ℕ,
        ({g ^ i * u * (g ^ i)⁻¹, g ^ i * v * (g ^ i)⁻¹, g ^ i * (u * v) * (g ^ i)⁻¹} : Set G) =
          {u', v', u' * v'}) := by
  obtain ⟨e, he⟩ := h.exists_basis
  have hxN : ∀ g : G, ∀ z ∈ zGroup Ω, g * z * g⁻¹ ∈ zGroup Ω :=
    fun g z hz => h.zGroup_normal.conj_mem z hz g
  obtain ⟨g₀, hg₀⟩ := h.dewb3_exists_conjMat he dewb3_A7_order.2.2
  obtain ⟨g, hg7, hgA⟩ := h.dewb3_lift he (n := 7) ⟨3, rfl⟩ (by norm_num)
    (by rw [hg₀, dewb3_A7_order.1])
  have hA : TL4.conjMat he g = dewb3_A7 := hgA.trans hg₀
  have hg1 : g ≠ 1 := by
    intro h1
    apply dewb3_A7_order.2.1
    rw [← hA, h1, TL4.conjMat_one he]
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpow : ∀ (i : ℕ) (c : Fin 3 → ZMod 2),
      g ^ i * TL4.e8Coord e c * (g ^ i)⁻¹ = TL4.e8Coord e ((dewb3_A7 ^ i).mulVec c) := by
    intro i c
    rw [TL4.conj_e8Coord he (hxN (g ^ i)) c, h.dewb3_conjMat_pow he g i, hA]
  refine ⟨g, orderOf_eq_prime hg7 hg1, ?_, ?_⟩
  · intro x hx hx1 y hy hy1
    obtain ⟨a, rfl⟩ := TL4.exists_e8Coord_eq he hx
    obtain ⟨b, rfl⟩ := TL4.exists_e8Coord_eq he hy
    have ha0 : a ≠ 0 := fun h0 => hx1 (by rw [h0, TL4.e8Coord_zero])
    have hb0 : b ≠ 0 := fun h0 => hy1 (by rw [h0, TL4.e8Coord_zero])
    obtain ⟨i, hi⟩ := dewb3_fin_regular a b ha0 hb0
    exact ⟨i, by rw [hpow, hi]⟩
  · intro u hu v hv hu1 hv1 huv u' hu' v' hv' hu'1 hv'1 hu'v'
    obtain ⟨a, rfl⟩ := TL4.exists_e8Coord_eq he hu
    obtain ⟨b, rfl⟩ := TL4.exists_e8Coord_eq he hv
    obtain ⟨a', rfl⟩ := TL4.exists_e8Coord_eq he hu'
    obtain ⟨b', rfl⟩ := TL4.exists_e8Coord_eq he hv'
    have ha0 : a ≠ 0 := fun h0 => hu1 (by rw [h0, TL4.e8Coord_zero])
    have hb0 : b ≠ 0 := fun h0 => hv1 (by rw [h0, TL4.e8Coord_zero])
    have hab : a ≠ b := fun h0 => huv (by rw [h0])
    have ha0' : a' ≠ 0 := fun h0 => hu'1 (by rw [h0, TL4.e8Coord_zero])
    have hb0' : b' ≠ 0 := fun h0 => hv'1 (by rw [h0, TL4.e8Coord_zero])
    have hab' : a' ≠ b' := fun h0 => hu'v' (by rw [h0])
    obtain ⟨i, hi⟩ := dewb3_fin_lines a b a' b' ha0 hb0 hab ha0' hb0' hab'
    refine ⟨(i : ℕ), ?_⟩
    have hS : ({(dewb3_A7 ^ (i : ℕ)).mulVec a, (dewb3_A7 ^ (i : ℕ)).mulVec b,
        (dewb3_A7 ^ (i : ℕ)).mulVec (a + b)} : Set (Fin 3 → ZMod 2)) = {a', b', a' + b'} := by
      have h2 := congrArg (fun s : Finset (Fin 3 → ZMod 2) => (s : Set (Fin 3 → ZMod 2))) hi
      simpa only [Finset.coe_insert, Finset.coe_singleton] using h2
    have himg : ∀ p q r : Fin 3 → ZMod 2,
        ({TL4.e8Coord e p, TL4.e8Coord e q, TL4.e8Coord e r} : Set G) =
          TL4.e8Coord e '' {p, q, r} := by
      intro p q r
      simp only [Set.image_insert_eq, Set.image_singleton]
    rw [← TL4.e8Coord_add he a b, ← TL4.e8Coord_add he a' b', hpow, hpow, hpow, himg, himg, hS]

end DE4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
