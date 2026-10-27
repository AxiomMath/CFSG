module

public import CFSG.GF2Type.SmithTypeE.L6.ModConj
public import Certificates.Certificate38671

public section

namespace CFSG.GF2Type.SmithTypeE.L6Ident

open CFSG.SmithL6 CFSG.GF2Type.SmithTypeE.LMod
open CFSG.SmithE (applyCols)
open CFSG.LargeExtraspecial.SMod20 (V decode decode_apply eq_of_decode_eq decode_two_pow)


attribute [local irreducible] CFSG.SmithL6.tvImg CFSG.SmithL6.tvIdxTab

theorem c8Check_holds : eaChkC8 = true := Certificates.certificate38671.1

theorem wCheck_holds : eaChkW = true := Certificates.certificate38671.2.1

theorem f4Check_holds : eaChkF4 = true := Certificates.certificate38671.2.2.1

theorem rigCheck_holds : eaChkRig = true := Certificates.certificate38671.2.2.2

@[expose] def C8 : Submodule (ZMod 2) V where
  carrier := {v | ∀ m : Fin 20, m.val ∉ eaBits → v m = 0}
  add_mem' := fun {a b} ha hb m hm => by
    simp only [Pi.add_apply, ha m hm, hb m hm, add_zero]
  zero_mem' := fun m _ => rfl
  smul_mem' := fun c v hv m hm => by
    simp only [Pi.smul_apply, hv m hm, smul_zero]

theorem mem_C8 {v : V} : v ∈ C8 ↔ ∀ m : Fin 20, m.val ∉ eaBits → v m = 0 := Iff.rfl

theorem eaSupp_iff {c : Nat} : eaSupp c = true ↔ decode c ∈ C8 := by
  rw [mem_C8]
  simp only [eaSupp, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h m hm
    rcases h m.val m.2 with h1 | h1
    · exact absurd (List.elem_iff.mp h1) hm
    · rw [decode_apply, h1]
      rfl
  · intro h m hm
    by_cases hb : m ∈ eaBits
    · exact Or.inl (List.elem_iff.mpr hb)
    · right
      have := h ⟨m, hm⟩ hb
      rw [decode_apply] at this
      by_contra hc
      simp only [Bool.not_eq_false] at hc
      rw [if_pos hc] at this
      exact one_ne_zero this

theorem tvEquiv_eq_self_iff {k : Nat} (hk : k < 1953) (v : V) :
    tvEquiv k v = v ↔ applyCols (tvCols k) (CFSG.LargeExtraspecial.S14.SMG.code v) =
      CFSG.LargeExtraspecial.S14.SMG.code v := by
  have hv := L6.decode_code v
  constructor
  · intro h
    refine eq_of_decode_eq (L6.applyCols_tv_lt hk _)
      (CFSG.LargeExtraspecial.S14.SMG.code_lt v) ?_
    rw [← tvEquiv_decode hk, hv, h]
  · intro h
    conv_lhs => rw [← hv]
    rw [tvEquiv_decode hk, h, hv]

theorem mem_C8_iff (v : V) : v ∈ C8 ↔ tvEquiv 0 v = v ∧ tvEquiv 31 v = v := by
  have h := c8Check_holds
  simp only [eaChkC8, List.all_eq_true, List.mem_range] at h
  have hc := h _ (CFSG.LargeExtraspecial.S14.SMG.code_lt v)
  have hmem : v ∈ C8 ↔ eaSupp (CFSG.LargeExtraspecial.S14.SMG.code v) = true := by
    rw [eaSupp_iff, L6.decode_code]
  rw [tvEquiv_eq_self_iff (by norm_num), tvEquiv_eq_self_iff (by norm_num), hmem,
    ← beq_iff_eq.mp hc]
  simp only [Bool.and_eq_true, beq_iff_eq]


theorem exists_wt_eq_two_pow {m : Nat} (hm : m ∈ eaBits) : ∃ i < 1395, wt i = 2 ^ m := by
  have h := wCheck_holds
  simp only [eaChkW, List.all_eq_true, List.any_eq_true, List.mem_range, beq_iff_eq] at h
  exact h m hm

theorem C8_le {N : Submodule (ZMod 2) V} (h : ∀ m : Fin 20, m.val ∈ eaBits → decode (2 ^ m.val) ∈ N) :
    C8 ≤ N := by
  intro v hv
  have hsum : v = ∑ m : Fin 20, v m • (Pi.single m (1 : ZMod 2) : V) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hsum]
  refine N.sum_mem fun m _ => ?_
  by_cases hm : m.val ∈ eaBits
  · rw [← decode_two_pow]
    exact N.smul_mem _ (h m hm)
  · rw [hv m hm, zero_smul]
    exact N.zero_mem

theorem tvImg_eq_of_commute {a b : Fin 1953} (h : Commute (tvP a) (tvP b)) :
    tvImg a b = b := by
  have h1 := mul_tvP_mul_inv (tvP_mem a) b
  rw [h.eq, mul_inv_cancel_right] at h1
  have h2 := tvP_injective h1
  rw [← tvP_apply, ← h2]

theorem commute_of_tvImg {a b : Fin 1953} (h : tvImg a b = b) : Commute (tvP a) (tvP b) := by
  have h1 := mul_tvP_mul_inv (tvP_mem a) b
  rw [show tvP a b = b from Fin.ext (by rw [tvP_apply]; exact h)] at h1
  exact mul_inv_eq_iff_eq_mul.mp h1

theorem mem_eaI {p : Fin 1953} (h0 : Commute (tvP p) (tvP 0)) (h31 : Commute (tvP p) (tvP 31)) :
    p.val ∈ eaI := by
  have e0 : tvImg p.val 0 = 0 := by simpa using tvImg_eq_of_commute h0
  have e31 : tvImg p.val 31 = 31 := by simpa using tvImg_eq_of_commute h31
  refine List.mem_filter.mpr ⟨List.mem_range.mpr p.2, ?_⟩
  rw [e0, e31]
  rfl

theorem lt_of_mem_eaI {p : Nat} (hp : p ∈ eaI) : p < 1953 :=
  List.mem_range.mp (List.mem_filter.mp hp).1

theorem commute_of_mem_eaI {p : Nat} (hp : p ∈ eaI) :
    Commute (tvP ⟨p, lt_of_mem_eaI hp⟩) (tvP 0) ∧ Commute (tvP ⟨p, lt_of_mem_eaI hp⟩) (tvP 31) := by
  have h2 := (List.mem_filter.mp hp).2
  simp only [Bool.and_eq_true, beq_iff_eq] at h2
  exact ⟨commute_of_tvImg (a := ⟨p, lt_of_mem_eaI hp⟩) (b := 0) h2.1,
    commute_of_tvImg (a := ⟨p, lt_of_mem_eaI hp⟩) (b := 31) h2.2⟩

theorem eq_of_restr_C8 {p s : Fin 1953} (hp0 : Commute (tvP p) (tvP 0))
    (hp31 : Commute (tvP p) (tvP 31)) (hs0 : Commute (tvP s) (tvP 0))
    (hs31 : Commute (tvP s) (tvP 31)) (h : ∀ v ∈ C8, tvEquiv p v = tvEquiv s v) : p = s := by
  by_contra hne
  have hF := f4Check_holds
  simp only [eaChkF4, List.all_eq_true, List.mem_map, Bool.or_eq_true, beq_iff_eq,
    bne_iff_ne, ne_eq, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hF
  rcases hF p.val (mem_eaI hp0 hp31) s.val (mem_eaI hs0 hs31) with h1 | h1
  · exact hne (Fin.ext h1)
  · apply h1
    simp only [eaRestr]
    refine List.map_congr_left fun m hm => ?_
    have hm20 : m < 20 := (by decide : ∀ x ∈ eaBits, x < 20) m hm
    have hv : decode (2 ^ m) ∈ C8 := by
      rw [show (2 ^ m : Nat) = 2 ^ (⟨m, hm20⟩ : Fin 20).val from rfl, decode_two_pow]
      intro j hj
      rw [Pi.single_apply, if_neg]
      intro e
      exact hj (e ▸ hm)
    have e := h _ hv
    rw [tvEquiv_decode p.2, tvEquiv_decode s.2] at e
    exact eq_of_decode_eq (L6.applyCols_tv_lt p.2 _) (L6.applyCols_tv_lt s.2 _) e

theorem eaRel_eq_of {a b a' b' : Nat} (h1 : a = b ↔ a' = b') (h2 : tvImg a b = b ↔ tvImg a' b' = b')
    (h3 : tvImg a b = tvImg b a ↔ tvImg a' b' = tvImg b' a') : eaRel a b = eaRel a' b' := by
  unfold eaRel
  exact if_congr h1 rfl (if_congr h2 rfl (if_congr h3 rfl rfl))

theorem eaRel_isTvAut {π : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π) (a b : Fin 1953) :
    eaRel (π a) (π b) = eaRel a b := by
  have hT : ∀ x y : Fin 1953, tvImg (π x) (π y) = ((π (tvP x y) : Fin 1953) : Nat) := fun x y => by
    rw [hπ.apply_tvP, tvP_apply]
  have hval : ∀ x y : Fin 1953, ((π x : Fin 1953) : Nat) = π y ↔ (x : Nat) = y := fun x y => by
    rw [← Fin.ext_iff, π.apply_eq_iff_eq, Fin.ext_iff]
  refine (eaRel_eq_of ?_ ?_ ?_).symm
  · exact (hval a b).symm
  · rw [hT, ← tvP_apply, hval]
  · rw [hT, hT, ← tvP_apply, ← tvP_apply, hval]

theorem fixed_of_eaUniq {π : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π) {F : List Nat}
    (hF : ∀ f ∈ F, ∃ hf : f < 1953, π ⟨f, hf⟩ = ⟨f, hf⟩) {q : Fin 1953}
    (hq : eaUniq F q = true) : π q = q := by
  simp only [eaUniq, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true, bne_iff_ne, ne_eq] at hq
  rcases hq (π q) (π q).2 with h | ⟨f, hf, hne⟩
  · exact Fin.ext h
  · exfalso
    obtain ⟨hf1953, hπf⟩ := hF f hf
    apply hne
    have := eaRel_isTvAut hπ q ⟨f, hf1953⟩
    rw [hπf] at this
    exact this.symm

theorem eq_one_of_isTvAut {π : Equiv.Perm (Fin 1953)} (hπ : IsTvAut π) (h0 : π 0 = 0)
    (h31 : π 31 = 31)
    (hI : ∀ p : Fin 1953, Commute (tvP p) (tvP 0) → Commute (tvP p) (tvP 31) → π p = p) :
    π = 1 := by
  have hbase : ∀ f ∈ eaBase, ∃ hf : f < 1953, π ⟨f, hf⟩ = ⟨f, hf⟩ := by
    intro f hf
    simp only [eaBase, List.mem_cons] at hf
    rcases hf with rfl | rfl | hf
    · exact ⟨by norm_num, h0⟩
    · exact ⟨by norm_num, h31⟩
    · exact ⟨lt_of_mem_eaI hf, hI _ (commute_of_mem_eaI hf).1 (commute_of_mem_eaI hf).2⟩
  have hF1 : ∀ f ∈ eaF1, ∃ hf : f < 1953, π ⟨f, hf⟩ = ⟨f, hf⟩ := by
    intro f hf
    simp only [eaF1, List.mem_filter, List.mem_range] at hf
    exact ⟨hf.1, fixed_of_eaUniq hπ hbase (q := ⟨f, hf.1⟩) hf.2⟩
  have hR := rigCheck_holds
  simp only [eaChkRig, List.all_eq_true, List.mem_range] at hR
  exact Equiv.ext fun q => fixed_of_eaUniq hπ hF1 (hR q q.2)

end CFSG.GF2Type.SmithTypeE.L6Ident
