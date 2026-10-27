module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec6Defs

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

open scoped commutatorElement

section Equiv

variable {X : Type} [Group X]

private theorem map_map_symm_aux (φ : X ≃* X) (K : Subgroup X) :
    (K.map φ.symm.toMonoidHom).map φ.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id X := by ext x; simp
  rw [this, Subgroup.map_id]

private theorem map_symm_map_aux (φ : X ≃* X) (K : Subgroup X) :
    (K.map φ.toMonoidHom).map φ.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id X := by ext x; simp
  rw [this, Subgroup.map_id]

private theorem map_eq_of_forall_map_le {F : Subgroup X → Subgroup X}
    (hF : ∀ (φ : X ≃* X) (H : Subgroup X), (F H).map φ.toMonoidHom ≤ F (H.map φ.toMonoidHom))
    (φ : X ≃* X) (H : Subgroup X) : (F H).map φ.toMonoidHom = F (H.map φ.toMonoidHom) := by
  refine le_antisymm (hF φ H) ?_
  have h := Subgroup.map_mono (f := φ.toMonoidHom) (hF φ.symm (H.map φ.toMonoidHom))
  rwa [map_map_symm_aux, map_symm_map_aux] at h

private theorem map_eq_of_forall_map_le' {F : X → Subgroup X}
    (hF : ∀ (φ : X ≃* X) (t : X), (F t).map φ.toMonoidHom ≤ F (φ t))
    (φ : X ≃* X) (t : X) : (F t).map φ.toMonoidHom = F (φ t) := by
  refine le_antisymm (hF φ t) ?_
  have h := Subgroup.map_mono (f := φ.toMonoidHom) (hF φ.symm (φ t))
  rwa [map_map_symm_aux, MulEquiv.symm_apply_apply] at h

theorem cen_map (φ : X ≃* X) (t : X) : (cen t).map φ.toMonoidHom = cen (φ t) :=
  (centralizer_singleton_map_mulEquiv φ t).symm

private theorem conj_apply_of_mem_cen {c t : X} (hc : c ∈ cen t) : MulAut.conj c t = t := by
  rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]

private theorem cen_le_normalizer_of_map {F : X → Subgroup X}
    (hF : ∀ (φ : X ≃* X) (t : X), (F t).map φ.toMonoidHom = F (φ t)) (t : X) :
    cen t ≤ normalizer (F t : Set X) := fun c hc =>
  mem_normalizer_of_map_conj_eq (by rw [hF, conj_apply_of_mem_cen hc])

theorem oddCoreOf_map_mulEquiv' (φ : X ≃* X) (H : Subgroup X) :
    (oddCoreOf H).map φ.toMonoidHom = oddCoreOf (H.map φ.toMonoidHom) :=
  (pPrimeCoreOf_map_mulEquiv φ H).symm

private theorem mem_map_mulEquiv_iff_aux (φ : X ≃* X) (K : Subgroup X) (x : X) :
    φ x ∈ K.map φ.toMonoidHom ↔ x ∈ K := by
  rw [Subgroup.mem_map_equiv]
  simp

private theorem normalizer_map_aux (φ : X ≃* X) (H : Subgroup X) :
    normalizer ((H.map φ.toMonoidHom : Subgroup X) : Set X) =
      (normalizer (H : Set X)).map φ.toMonoidHom :=
  (Subgroup.map_normalizer_eq_of_bijective H φ.bijective).symm

private theorem mem_normalizer_map_iff_aux (φ : X ≃* X) (K : Subgroup X) (x : X) :
    φ x ∈ normalizer ((K.map φ.toMonoidHom : Subgroup X) : Set X) ↔
      x ∈ normalizer (K : Set X) := by
  rw [normalizer_map_aux, mem_map_mulEquiv_iff_aux]

private theorem mem_centralizerSection_map_aux (φ : X ≃* X) (K M : Subgroup X) (x : X) :
    φ x ∈ centralizerSection (K.map φ.toMonoidHom) (M.map φ.toMonoidHom) ↔
      x ∈ centralizerSection K M := by
  show (φ x ∈ normalizer ((K.map φ.toMonoidHom : Subgroup X) : Set X) ∧
      φ x ∈ normalizer ((M.map φ.toMonoidHom : Subgroup X) : Set X) ∧
      ∀ k ∈ K.map φ.toMonoidHom, ⁅k, φ x⁆ ∈ M.map φ.toMonoidHom) ↔
    (x ∈ normalizer (K : Set X) ∧ x ∈ normalizer (M : Set X) ∧ ∀ k ∈ K, ⁅k, x⁆ ∈ M)
  rw [mem_normalizer_map_iff_aux, mem_normalizer_map_iff_aux]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h k hk
    have := h (φ k) ((mem_map_mulEquiv_iff_aux φ K k).2 hk)
    rw [← map_commutatorElement] at this
    exact (mem_map_mulEquiv_iff_aux φ M _).1 this
  · intro h k hk
    obtain ⟨k₀, hk₀, rfl⟩ := hk
    have h1 : ⁅φ.toMonoidHom k₀, φ x⁆ = φ ⁅k₀, x⁆ := (map_commutatorElement φ k₀ x).symm
    rw [h1]
    exact (mem_map_mulEquiv_iff_aux φ M _).2 (h k₀ hk₀)

theorem zStar_map_mulEquiv' (φ : X ≃* X) (H : Subgroup X) :
    (zStar H).map φ.toMonoidHom = zStar (H.map φ.toMonoidHom) := by
  ext y
  obtain ⟨x, rfl⟩ := φ.surjective y
  rw [mem_map_mulEquiv_iff_aux]
  show (x ∈ H ∧ x ∈ centralizerSection H (pPrimeCoreOf 2 H)) ↔
    (φ x ∈ H.map φ.toMonoidHom ∧
      φ x ∈ centralizerSection (H.map φ.toMonoidHom) (pPrimeCoreOf 2 (H.map φ.toMonoidHom)))
  rw [pPrimeCoreOf_map_mulEquiv, mem_centralizerSection_map_aux, mem_map_mulEquiv_iff_aux]

theorem IsSec6MType.congr {n : ℕ} {Q Q' : Type} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : IsSec6MType n Q) : IsSec6MType n Q' := by
  rcases h with ⟨hn, ⟨f⟩⟩ | ⟨hn, ⟨f⟩⟩
  · exact Or.inl ⟨hn, ⟨e.symm.trans f⟩⟩
  · exact Or.inr ⟨hn, ⟨e.symm.trans f⟩⟩

theorem IsMLIntrIn.map_mulEquiv (φ : X ≃* X) {H M : Subgroup X} (h : IsMLIntrIn X H M) :
    IsMLIntrIn X (H.map φ.toMonoidHom) (M.map φ.toMonoidHom) := by
  obtain ⟨⟨hMH, hpc⟩, hty, hJ⟩ := h
  obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv
    (Subgroup.equivMapOfInjective M φ.toMonoidHom φ.injective)
  refine ⟨⟨Subgroup.map_mono hMH,
    (isPComponent_subgroupOf_map_iff 2 φ.toMonoidHom φ.injective hMH).2 hpc⟩, ?_, ?_⟩
  · exact hty.imp (Nonempty.map f.symm.trans) (Nonempty.map f.symm.trans)
  · intro y hy hy2
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
    have hs2 : orderOf s = 2 := (MulEquiv.orderOf_eq φ s).symm.trans hy2
    obtain ⟨J, hJs, hJle⟩ := hJ s hs hs2
    have hC : centralizer ({φ.toMonoidHom s} : Set X) =
        (centralizer ({s} : Set X)).map φ.toMonoidHom :=
      centralizer_singleton_map_mulEquiv φ s
    refine ⟨J.map φ.toMonoidHom, hJs.map_mulEquiv φ, ?_⟩
    rw [hC, ← Subgroup.map_inf_eq _ _ _ φ.injective, ← oddCoreOf_map_mulEquiv',
      ← Subgroup.map_sup]
    exact Subgroup.map_mono hJle

theorem Sec6MComp.map_mulEquiv {n : ℕ} (φ : X ≃* X) {H M : Subgroup X}
    (h : Sec6MComp X n H M) : Sec6MComp X n (H.map φ.toMonoidHom) (M.map φ.toMonoidHom) := by
  obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv
    (Subgroup.equivMapOfInjective M φ.toMonoidHom φ.injective)
  exact ⟨h.1.map_mulEquiv φ, h.2.congr f⟩

theorem Sec6M_map (n : ℕ) (φ : X ≃* X) (H : Subgroup X) :
    (Sec6M X n H).map φ.toMonoidHom = Sec6M X n (H.map φ.toMonoidHom) := by
  refine map_eq_of_forall_map_le (F := Sec6M X n) (fun ψ K => ?_) φ H
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun M hM => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact le_sSup (Sec6MComp.map_mulEquiv ψ hM)

theorem Sec6K_map (n : ℕ) (φ : X ≃* X) (H : Subgroup X) :
    (Sec6K X n H).map φ.toMonoidHom = Sec6K X n (H.map φ.toMonoidHom) := by
  rw [sec6K_eq, sec6K_eq, Subgroup.map_sup, K0_map, Sec6M_map]

theorem map_conj_Sec6M (n : ℕ) {H : Subgroup X} {c : X} (hc : c ∈ normalizer (H : Set X)) :
    (Sec6M X n H).map (MulAut.conj c).toMonoidHom = Sec6M X n H := by
  rw [Sec6M_map, map_conj_eq_of_mem_normalizer hc]

theorem map_conj_Sec6K (n : ℕ) {H : Subgroup X} {c : X} (hc : c ∈ normalizer (H : Set X)) :
    (Sec6K X n H).map (MulAut.conj c).toMonoidHom = Sec6K X n H := by
  rw [Sec6K_map, map_conj_eq_of_mem_normalizer hc]

theorem K0_cen_normal (n : ℕ) (t : X) : cen t ≤ normalizer (K0 X n (cen t) : Set X) :=
  fun _ hc => mem_normalizer_of_map_conj_eq (map_conj_K0 n (Subgroup.le_normalizer hc))

theorem Sec6M_cen_normal (n : ℕ) (t : X) : cen t ≤ normalizer (Sec6M X n (cen t) : Set X) :=
  fun _ hc => mem_normalizer_of_map_conj_eq (map_conj_Sec6M n (Subgroup.le_normalizer hc))

theorem Sec6K_cen_normal (n : ℕ) (t : X) : cen t ≤ normalizer (Sec6K X n (cen t) : Set X) :=
  fun _ hc => mem_normalizer_of_map_conj_eq (map_conj_Sec6K n (Subgroup.le_normalizer hc))

theorem Sec6Base_map (n : ℕ) (φ : X ≃* X) (t : X) :
    (Sec6Base X n t).map φ.toMonoidHom = Sec6Base X n (φ t) := by
  unfold Sec6Base
  rw [Subgroup.map_sup, Sec6M_map, zStar_map_mulEquiv', K0_map, cen_map]

private theorem map_iSup_inv_le (φ : X ≃* X) {B B' : Subgroup X} {F F' : X → Subgroup X}
    (hB : B.map φ.toMonoidHom ≤ B') (hF : ∀ x, (F x).map φ.toMonoidHom ≤ F' (φ x)) :
    (⨆ (x : X) (_ : x ∈ B) (_ : orderOf x = 2), F x).map φ.toMonoidHom ≤
      ⨆ (y : X) (_ : y ∈ B') (_ : orderOf y = 2), F' y := by
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun hx2 => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have hy : φ x ∈ B' := hB (Subgroup.mem_map_of_mem _ hx)
  have hy2 : orderOf (φ x) = 2 := (MulEquiv.orderOf_eq φ x).trans hx2
  exact (hF x).trans (le_iSup_of_le (φ x) (le_iSup_of_le hy (le_iSup_of_le hy2 le_rfl)))

theorem sec6Sig_map (n : ℕ) (φ : X ≃* X) (t : X) :
    (sec6Sig X n t).map φ.toMonoidHom = sec6Sig X n (φ t) := by
  refine map_eq_of_forall_map_le' (F := sec6Sig X n) (fun ψ s => ?_) φ t
  unfold sec6Sig
  refine map_iSup_inv_le ψ (le_of_eq ?_) fun x => le_of_eq ?_
  · rw [Sec6M_map, cen_map]
  · rw [oddCoreOf_map_mulEquiv', cen_map]

theorem sec6V_map (n : ℕ) (φ : X ≃* X) (t : X) :
    (sec6V X n t).map φ.toMonoidHom = sec6V X n (φ t) := by
  refine map_eq_of_forall_map_le' (F := sec6V X n) (fun ψ s => ?_) φ t
  unfold sec6V
  refine map_iSup_inv_le ψ (le_of_eq ?_) fun x => le_of_eq ?_
  · rw [Sec6M_map, cen_map]
  · rw [Sec6K_map, cen_map]

theorem cen_le_normalizer_sec6Base (n : ℕ) (t : X) :
    cen t ≤ normalizer (Sec6Base X n t : Set X) :=
  cen_le_normalizer_of_map (Sec6Base_map n) t

theorem cen_le_normalizer_sec6Sig (n : ℕ) (t : X) :
    cen t ≤ normalizer (sec6Sig X n t : Set X) :=
  cen_le_normalizer_of_map (sec6Sig_map n) t

theorem cen_le_normalizer_sec6V (n : ℕ) (t : X) :
    cen t ≤ normalizer (sec6V X n t : Set X) :=
  cen_le_normalizer_of_map (sec6V_map n) t

end Equiv

end CFSG.OddStandard.Solomon75
