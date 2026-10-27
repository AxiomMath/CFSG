module

public import CFSG.ClassicalInvolution.Q3.Sec13E4Shult
public import CFSG.ClassicalInvolution.Q3.Sec13AE5Model

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def sig (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5)) :
    G →* Equiv.Perm (Fin 5) :=
  (alternatingGroup (Fin 5)).subtype.comp (a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G)))

theorem sig_mem (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5)) (g : G) :
    sig a g ∈ alternatingGroup (Fin 5) :=
  (a (QuotientGroup.mk' (pCore 2 G) g)).2

theorem sig_eq_one_iff (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5)) {g : G} :
    sig a g = 1 ↔ g ∈ pCore 2 G := by
  constructor
  · intro hg
    have h1 : a (QuotientGroup.mk' (pCore 2 G) g) = 1 := Subtype.ext hg
    have h2 : QuotientGroup.mk' (pCore 2 G) g = 1 := a.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff g).mp h2
  · intro hg
    have h2 : QuotientGroup.mk' (pCore 2 G) g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    have h1 : a (QuotientGroup.mk' (pCore 2 G) g) = 1 := by rw [h2, map_one]
    exact congrArg Subtype.val h1

theorem exists_sig_eq (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))
    (x : alternatingGroup (Fin 5)) : ∃ g : G, sig a g = x := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (a.symm x)
  refine ⟨g, ?_⟩
  have h1 : QuotientGroup.mk' (pCore 2 G) g = a.symm x := hg
  have h2 : a (QuotientGroup.mk' (pCore 2 G) g) = x := by
    rw [h1, MulEquiv.apply_symm_apply]
  exact congrArg Subtype.val h2

@[expose] def IsOver (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5)) (L : Subgroup G)
    (γ : Fin 5) : Prop :=
  ∀ l ∈ L, sig a l γ = γ

theorem isOver_conj (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5)) {L : Subgroup G}
    {γ : Fin 5} (hL : IsOver a L γ) (g : G) : IsOver a (conjSub g L) (sig a g γ) := by
  intro l hl
  rw [mem_conjSub_iff] at hl
  have h1 := hL _ hl
  have e : l * g = g * (g⁻¹ * l * g) := by group
  calc sig a l (sig a g γ) = sig a (l * g) γ := by rw [map_mul]; rfl
    _ = sig a (g * (g⁻¹ * l * g)) γ := by rw [e]
    _ = sig a g (sig a (g⁻¹ * l * g) γ) := by rw [map_mul]; rfl
    _ = sig a g γ := by rw [h1]

private theorem exists_sig_apply_eq₂ (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))
    {γ δ γ' δ' : Fin 5} (h : γ ≠ δ) (h' : γ' ≠ δ') :
    ∃ g : G, sig a g γ = γ' ∧ sig a g δ = δ' := by
  obtain ⟨x, hx1, hx2⟩ := A5.exists_two_trans γ δ γ' δ' h h'
  obtain ⟨g, hg⟩ := exists_sig_eq a x
  exact ⟨g, by rw [hg]; exact hx1, by rw [hg]; exact hx2⟩

private theorem exists_sig_apply_eq (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))
    (γ γ' : Fin 5) : ∃ g : G, sig a g γ = γ' := by
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin 5, δ ≠ γ := ⟨γ + 1, by revert γ; decide⟩
  obtain ⟨δ', hδ'⟩ : ∃ δ' : Fin 5, δ' ≠ γ' := ⟨γ' + 1, by revert γ'; decide⟩
  obtain ⟨g, hg, -⟩ := exists_sig_apply_eq₂ a hδ.symm hδ'.symm
  exact ⟨g, hg⟩

private theorem isOver_iff_bar (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))
    (L : Subgroup G) (γ : Fin 5) :
    IsOver a L γ ↔
      ∀ x ∈ bar L, ((a x : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) γ = γ := by
  constructor
  · intro hγ x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    exact hγ l hl
  · intro hγ l hl
    exact hγ _ (Subgroup.mem_map_of_mem _ hl)

private theorem isOver_of_bar_eq (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))
    {K L : Subgroup G} {γ : Fin 5} (hKL : bar K = bar L) (hL : IsOver a L γ) :
    IsOver a K γ := by
  rw [isOver_iff_bar] at hL ⊢
  rw [hKL]
  exact hL

private noncomputable abbrev imgA5 (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))
    (L : Subgroup G) : Subgroup (alternatingGroup (Fin 5)) :=
  (bar L).map a.toMonoidHom

private theorem isOver_iff_imgA5 (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))
    (L : Subgroup G) (γ : Fin 5) :
    IsOver a L γ ↔ ∀ e ∈ imgA5 a L, (e : Equiv.Perm (Fin 5)) γ = γ := by
  constructor
  · intro hγ e he
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    exact hγ l hl
  · intro hγ l hl
    exact hγ (a (QuotientGroup.mk' (pCore 2 G) l))
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hl))

private theorem prod_perm_eq {f : Fin 5 → G} (hf : ∀ i j, f i * f j = f j * f i)
    (σ : Equiv.Perm (Fin 5)) :
    f (σ 0) * f (σ 1) * f (σ 2) * f (σ 3) * f (σ 4) = f 0 * f 1 * f 2 * f 3 * f 4 := by
  letI : CommGroup (Subgroup.closure (Set.range f)) :=
    Subgroup.closureCommGroupOfComm (fun x hx y hy _ => by
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, rfl⟩ := hy
      exact hf i j)
  let F : Fin 5 → Subgroup.closure (Set.range f) :=
    fun i => ⟨f i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have h1 : ∏ i, F (σ i) = ∏ i, F i := Equiv.prod_comp σ F
  rw [Fin.prod_univ_five, Fin.prod_univ_five] at h1
  exact congrArg Subtype.val h1

namespace E4Hyp

variable {Ω : Set (Subgroup G)} {W : Subgroup G} (h : E4Hyp Ω W)
  (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))
include h

private theorem card_imgA5 {L : Subgroup G} (hL : L ∈ Ω) : Nat.card (imgA5 a L) = 4 := by
  rw [imgA5, Subgroup.card_map_of_injective (f := a.toMonoidHom) a.injective, h.card_bar hL]

private theorem sq_imgA5 {L : Subgroup G} (hL : L ∈ Ω) {e : alternatingGroup (Fin 5)}
    (he : e ∈ imgA5 a L) : e * e = 1 := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he
  have h2 := (h.isElemAbelian_bar hL).2 x hx
  show a x * a x = 1
  rw [← map_mul, ← pow_two, h2, map_one]

private theorem comm_imgA5 {L : Subgroup G} (hL : L ∈ Ω) {e f : alternatingGroup (Fin 5)}
    (he : e ∈ imgA5 a L) (hf : f ∈ imgA5 a L) : e * f = f * e := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hf
  have h2 : x * y = y * x :=
    congrArg Subtype.val ((h.isElemAbelian_bar hL).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  show a x * a y = a y * a x
  rw [← map_mul, ← map_mul, h2]

theorem existsUnique_over {L : Subgroup G} (hL : L ∈ Ω) : ∃! γ : Fin 5, IsOver a L γ := by
  have hcard : 2 < (↑(imgA5 a L) : Set (alternatingGroup (Fin 5))).ncard := by
    have h1 : Nat.card (imgA5 a L) = (↑(imgA5 a L) : Set (alternatingGroup (Fin 5))).ncard :=
      Nat.card_coe_set_eq _
    have := h.card_imgA5 a hL
    omega
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 hcard
  obtain ⟨u, v, hu, hv, hu1, hv1, huv⟩ : ∃ u v : alternatingGroup (Fin 5), u ∈ imgA5 a L ∧
      v ∈ imgA5 a L ∧ u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
    by_cases hx1 : x = 1
    · exact ⟨y, z, hy, hz, fun h1 => hxy (hx1.trans h1.symm), fun h1 => hxz (hx1.trans h1.symm),
        hyz⟩
    · by_cases hy1 : y = 1
      · exact ⟨x, z, hx, hz, hx1, fun h1 => hyz (hy1.trans h1.symm), hxz⟩
      · exact ⟨x, y, hx, hy, hx1, hy1, hxy⟩
  have hu2 := h.sq_imgA5 a hL hu
  have hv2 := h.sq_imgA5 a hL hv
  have huv' := h.comm_imgA5 a hL hu hv
  obtain ⟨γ, ⟨hγu, hγv⟩, hγ⟩ := A5.existsUnique_fixed u v hu1 hv1 huv hu2 hv2 huv'
  refine ⟨γ, (isOver_iff_imgA5 a L γ).mpr fun e he => ?_, fun y hy => ?_⟩
  · refine hγ _ ⟨?_, ?_⟩
    · have h1 : (u : Equiv.Perm (Fin 5)) ((e : Equiv.Perm (Fin 5)) γ) =
          (e : Equiv.Perm (Fin 5)) ((u : Equiv.Perm (Fin 5)) γ) :=
        congrArg (fun x : alternatingGroup (Fin 5) => (x : Equiv.Perm (Fin 5)) γ)
          (h.comm_imgA5 a hL hu he)
      rw [h1, hγu]
    · have h1 : (v : Equiv.Perm (Fin 5)) ((e : Equiv.Perm (Fin 5)) γ) =
          (e : Equiv.Perm (Fin 5)) ((v : Equiv.Perm (Fin 5)) γ) :=
        congrArg (fun x : alternatingGroup (Fin 5) => (x : Equiv.Perm (Fin 5)) γ)
          (h.comm_imgA5 a hL hv he)
      rw [h1, hγv]
  · exact hγ y ⟨(isOver_iff_imgA5 a L y).mp hy u hu, (isOver_iff_imgA5 a L y).mp hy v hv⟩

theorem inv_eq_of_isOver {L L' : Subgroup G} (hL : L ∈ Ω) (hL' : L' ∈ Ω) {γ : Fin 5}
    (hγ : IsOver a L γ) (hγ' : IsOver a L' γ) {z z' : G} (hz : IsUniqueInvolution L z)
    (hz' : IsUniqueInvolution L' z') : z = z' := by
  obtain ⟨S, hSmem, hScard⟩ : ∃ S : Finset (alternatingGroup (Fin 5)),
      (∀ u, u ∈ S ↔ (u * u = 1 ∧ (u : Equiv.Perm (Fin 5)) γ = γ)) ∧ S.card = 4 :=
    ⟨_, fun u => by simp, A5.card_filter_inv_fix γ⟩
  have himg : ∀ {K : Subgroup G}, K ∈ Ω → IsOver a K γ →
      (↑(imgA5 a K) : Set (alternatingGroup (Fin 5))) = ↑S := by
    intro K hK hKγ
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro e he
      exact (hSmem e).mpr ⟨h.sq_imgA5 a hK he, (isOver_iff_imgA5 a K γ).mp hKγ e he⟩
    · have h1 : Nat.card (imgA5 a K) = (↑(imgA5 a K) : Set (alternatingGroup (Fin 5))).ncard :=
        Nat.card_coe_set_eq _
      have h2 := h.card_imgA5 a hK
      rw [Set.ncard_coe_finset]
      omega
  have himg_eq : imgA5 a L = imgA5 a L' :=
    SetLike.coe_injective ((himg hL hγ).trans (himg hL' hγ').symm)
  have hbar : bar L = bar L' := Subgroup.map_injective (f := a.toMonoidHom) a.injective himg_eq
  have hle : L' ≤ L ⊔ pCore 2 G :=
    calc L' ≤ L' ⊔ pCore 2 G := le_sup_left
      _ = (bar L').comap (QuotientGroup.mk' (pCore 2 G)) := (comap_bar L').symm
      _ = (bar L).comap (QuotientGroup.mk' (pCore 2 G)) := by rw [hbar]
      _ = L ⊔ pCore 2 G := comap_bar L
  obtain ⟨J, hp⟩ := h.exists_partner hL
  rcases h.eq_or_eq_of_le_sup hp hL' hle with rfl | rfl
  · exact hz.eq hz'
  · exact h.inv_eq hp hz hz'

theorem exists_over (γ : Fin 5) : ∃ L ∈ Ω, IsOver a L γ := by
  obtain ⟨A, B, hp⟩ := h.exists_paired
  obtain ⟨γ₀, hγ₀, -⟩ := h.existsUnique_over a hp.1
  obtain ⟨g, hg⟩ := exists_sig_apply_eq a γ₀ γ
  refine ⟨conjSub g A, h.thmD.hyp.conjInvariant g A hp.1, ?_⟩
  have := isOver_conj a hγ₀ g
  rwa [hg] at this

omit h in
@[expose] noncomputable def w (h : E4Hyp Ω W) (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5))
    (γ : Fin 5) : G :=
  ((h.exists_over a γ).choose_spec.1 |> fun hL =>
    (h.exists_uniqueInvolution hL).choose)

theorem w_spec (γ : Fin 5) :
    ∃ L ∈ Ω, IsOver a L γ ∧ IsUniqueInvolution L (h.w a γ) := by
  have hex := (h.exists_over a γ).choose_spec
  exact ⟨_, hex.1, hex.2, (h.exists_uniqueInvolution hex.1).choose_spec⟩

theorem w_eq {L : Subgroup G} (hL : L ∈ Ω) {γ : Fin 5} (hγ : IsOver a L γ) {z : G}
    (hz : IsUniqueInvolution L z) : h.w a γ = z := by
  obtain ⟨L', hL', hγ', hz'⟩ := h.w_spec a γ
  exact h.inv_eq_of_isOver a hL' hL hγ' hγ hz' hz

theorem w_mem_pCore (γ : Fin 5) : h.w a γ ∈ pCore 2 G := by
  obtain ⟨L, hL, -, hz⟩ := h.w_spec a γ
  exact h.mem_pCore hL hz

theorem w_ne_one (γ : Fin 5) : h.w a γ ≠ 1 := by
  obtain ⟨L, -, -, hz⟩ := h.w_spec a γ
  exact hz.ne_one

theorem w_mul_self (γ : Fin 5) : h.w a γ * h.w a γ = 1 := by
  obtain ⟨L, -, -, hz⟩ := h.w_spec a γ
  exact hz.sq

theorem conj_w (g : G) (γ : Fin 5) : g * h.w a γ * g⁻¹ = h.w a (sig a g γ) := by
  obtain ⟨L, hL, hγ, hz⟩ := h.w_spec a γ
  exact (h.w_eq a (h.thmD.hyp.conjInvariant g L hL) (isOver_conj a hγ g) (hz.conj g)).symm

theorem w_comm (γ δ : Fin 5) : h.w a γ * h.w a δ = h.w a δ * h.w a γ := by
  by_cases hγδ : γ = δ
  · rw [hγδ]
  obtain ⟨L, hL, hLγ, hLz⟩ := h.w_spec a γ
  obtain ⟨M, hM, hMδ, hMz⟩ := h.w_spec a δ
  obtain ⟨L', hp⟩ := h.exists_partner hL
  have hL'γ : IsOver a L' γ := isOver_of_bar_eq a (h.bar_eq_of_paired hp).symm hLγ
  have hML : M ≠ L := by
    rintro rfl
    exact hγδ ((h.existsUnique_over a hM).unique hLγ hMδ)
  have hML' : M ≠ L' := by
    rintro rfl
    exact hγδ ((h.existsUnique_over a hM).unique hL'γ hMδ)
  have hswap : conjSub (h.w a δ) L = L' := h.swap hp hM hML hML' hMz
  have hconj := hLz.conj (h.w a δ)
  rw [hswap] at hconj
  have e : h.w a γ = h.w a δ * h.w a γ * (h.w a δ)⁻¹ := h.w_eq a hp.2.1 hL'γ hconj
  exact (mul_inv_eq_iff_eq_mul.mp e.symm).symm

theorem prod_w : h.w a 0 * h.w a 1 * h.w a 2 * h.w a 3 * h.w a 4 = 1 := by
  have hcen : (h.w a 0 * h.w a 1 * h.w a 2 * h.w a 3 * h.w a 4) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have e : g * (h.w a 0 * h.w a 1 * h.w a 2 * h.w a 3 * h.w a 4) * g⁻¹ =
        (g * h.w a 0 * g⁻¹) * (g * h.w a 1 * g⁻¹) * (g * h.w a 2 * g⁻¹) *
          (g * h.w a 3 * g⁻¹) * (g * h.w a 4 * g⁻¹) := by group
    rw [h.conj_w a g 0, h.conj_w a g 1, h.conj_w a g 2, h.conj_w a g 3, h.conj_w a g 4,
      prod_perm_eq (h.w_comm a) (sig a g)] at e
    exact mul_inv_eq_iff_eq_mul.mp e
  rw [h.center, Subgroup.mem_bot] at hcen
  exact hcen

theorem w_ne (γ δ : Fin 5) (hγδ : γ ≠ δ) : h.w a γ ≠ h.w a δ := by
  intro heq
  have hall : ∀ i : Fin 5, h.w a i = h.w a 0 := by
    intro i
    by_cases hi : i = 0
    · rw [hi]
    · obtain ⟨g, hg1, hg2⟩ := exists_sig_apply_eq₂ a hγδ hi
      have e1 := h.conj_w a g γ
      have e2 := h.conj_w a g δ
      rw [hg1] at e1
      rw [hg2] at e2
      rw [← e1, ← e2, heq]
  have hp := h.prod_w a
  rw [hall 1, hall 2, hall 3, hall 4] at hp
  have hsq := h.w_mul_self a 0
  have h5 : h.w a 0 * h.w a 0 * h.w a 0 * h.w a 0 * h.w a 0 = h.w a 0 :=
    calc h.w a 0 * h.w a 0 * h.w a 0 * h.w a 0 * h.w a 0
        = (h.w a 0 * h.w a 0) * (h.w a 0 * h.w a 0) * h.w a 0 := by group
      _ = h.w a 0 := by rw [hsq]; group
  exact h.w_ne_one a 0 (h5.symm.trans hp)

end E4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
