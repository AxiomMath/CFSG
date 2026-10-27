module

public import Certificates.Data.GH74EvSporCheck

public section

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open scoped commutatorElement

namespace CFSG.GH74.Generic.S45.EvSpor

variable {n : ℕ}

@[expose] def EnumsSub (n : ℕ) (E : Array Table) (H : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  (∀ k < E.size, ∃ c ∈ H, Rep n E[k]! c) ∧ (∀ x ∈ H, ∃ k < E.size, Rep n E[k]! x)

theorem EnumsSub.mem_iff {E : Array Table} {H : Subgroup (Equiv.Perm (Fin n))} (hE : EnumsSub n E H)
    {y : Table} {g : Equiv.Perm (Fin n)} (hy : Rep n y g) : memT n E y = true ↔ g ∈ H := by
  constructor
  · intro h
    rw [memT, Array.any_eq_true] at h
    obtain ⟨k, hk, hyk⟩ := h
    obtain ⟨c, hc, hrep⟩ := hE.1 k hk
    rw [← getElem!_pos E k hk] at hyk
    have h1 : Rep n y c := rep_of_tblEq hrep hyk
    rwa [rep_unique hy h1]
  · intro hg
    obtain ⟨k, hk, hrep⟩ := hE.2 g hg
    rw [memT, Array.any_eq_true]
    refine ⟨k, hk, ?_⟩
    rw [← getElem!_pos E k hk]
    exact (tblEq_iff_eq hy hrep).2 rfl

theorem EnumsSub.forall {E : Array Table} {H : Subgroup (Equiv.Perm (Fin n))} (hE : EnumsSub n E H)
    {p : Table → Bool} {P : Equiv.Perm (Fin n) → Prop}
    (hp : ∀ T g, Rep n T g → p T = true → P g) (h : E.all p = true) : ∀ x ∈ H, P x := by
  intro x hx
  obtain ⟨k, hk, hrep⟩ := hE.2 x hx
  rw [Array.all_eq_true] at h
  have := h k hk
  rw [← getElem!_pos E k hk] at this
  exact hp _ _ hrep this

theorem EnumsSub.rep_mem {E : Array Table} {H : Subgroup (Equiv.Perm (Fin n))} (hE : EnumsSub n E H)
    {x : Equiv.Perm (Fin n)} (hx : x ∈ H) : ∃ T ∈ E, Rep n T x := by
  obtain ⟨k, hk, hrep⟩ := hE.2 x hx
  exact ⟨E[k]!, by rw [getElem!_pos E k hk]; exact Array.getElem_mem hk, hrep⟩

theorem enumOK_spec (hn : n < 2 ^ 32) {cap : ℕ} {gs : List Table} {sz : ℕ}
    (h : enumOK n cap gs sz = true) :
    EnumsSub n (closArr n cap gs) (closure (tp n '' {x | x ∈ gs.toArray})) ∧
      Nat.card ↥(closure (tp n '' {x | x ∈ gs.toArray})) = sz ∧
      ∀ g ∈ gs, Rep n g (tp n g) := by
  simp only [enumOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hg, htree⟩, hclosed⟩, hdist⟩, hsize⟩ := h
  have hg' : ∀ x ∈ gs.toArray, permOK n x = true := fun x hx => by
    exact (hg x (List.mem_toArray.mp hx)).1
  have hginv : ∀ x ∈ gs.toArray, invOK n x (invT n x) = true := fun x hx => by
    exact (hg x (List.mem_toArray.mp hx)).2
  obtain ⟨h1, h2, h3⟩ := enum_spec hn hg' hginv htree hclosed hdist
  refine ⟨⟨fun k hk => ⟨_, (h1 k hk).2, (h1 k hk).1⟩, fun x hx => h2 x hx⟩, h3.trans hsize, ?_⟩
  intro g hgs
  exact rep_tp (hg' g (List.mem_toArray.mpr hgs))


theorem invT_eq_foldl (n : ℕ) (P : Table) :
    invT n P = (List.range' 0 n).foldl
      (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0) := by
  unfold invT
  simp [Id.run]
  rfl

theorem invT_foldl_spec {n : ℕ} (P : Table) (hlt : ∀ i < n, (P[i]!).toNat < n)
    (hinj : ∀ i < n, ∀ i' < n, (P[i]!).toNat = (P[i']!).toNat → i = i') :
    ∀ m ≤ n, ((List.range' 0 m).foldl
        (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (Array.replicate n 0)).size = n ∧
      ∀ i < m, ((List.range' 0 m).foldl
        (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i))
          (Array.replicate n 0))[(P[i]!).toNat]! = UInt32.ofNat i := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    obtain ⟨hs, hi⟩ := ih (by omega)
    rw [List.range'_concat, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [zero_add, one_mul]
    set r := (List.range' 0 m).foldl (fun r i => r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i))
      (Array.replicate n 0) with hr
    refine ⟨by rw [Array.size_setIfInBounds, hs], fun i hi' => ?_⟩
    have hmn : m < n := by omega
    have hPm := hlt m hmn
    have hbound : (P[m]!).toNat < (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)).size := by
      rw [Array.size_setIfInBounds, hs]; exact hPm
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hlt' | heq
    · have hne : (P[m]!).toNat ≠ (P[i]!).toNat := fun h' => by
        have := hinj m hmn i (by omega) h'
        omega
      have hbi : (P[i]!).toNat < r.size := by rw [hs]; exact hlt i (by omega)
      have hbi' : (P[i]!).toNat < (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)).size := by
        rw [Array.size_setIfInBounds]; exact hbi
      rw [getElem!_pos (r.setIfInBounds (P[m]!).toNat (UInt32.ofNat m)) (P[i]!).toNat hbi',
        Array.getElem_setIfInBounds_ne hbi hne, ← getElem!_pos r (P[i]!).toNat hbi]
      exact hi i hlt'
    · subst heq
      rw [getElem!_pos (r.setIfInBounds (P[i]!).toNat (UInt32.ofNat i)) (P[i]!).toNat hbound,
        Array.getElem_setIfInBounds_self]

theorem invOK_invT {n : ℕ} (hn : n < 2 ^ 32) (P : Table) (hlt : ∀ i < n, (P[i]!).toNat < n)
    (hinj : ∀ i < n, ∀ i' < n, (P[i]!).toNat = (P[i']!).toNat → i = i') :
    invOK n P (invT n P) = true := by
  rw [invOK, allIn_eq_true]
  intro i _ hi
  have h := (invT_foldl_spec P hlt hinj n le_rfl).2 i hi
  rw [← invT_eq_foldl] at h
  rw [beq_iff_eq]
  unfold ap
  rw [h, UInt32.toNat_ofNat', Nat.mod_eq_of_lt (hi.trans hn)]

theorem rep_invT_of_rep {n : ℕ} (hn : n < 2 ^ 32) {T : Table} {g : Equiv.Perm (Fin n)}
    (hT : Rep n T g) : Rep n (invT n T) g⁻¹ := by
  refine Rep.inv_of_invOK hT (invOK_invT hn T ?_ ?_)
  · intro i hi
    have := hT i hi
    unfold ap at this
    rw [this]
    exact idx_lt g hi
  · intro i hi i' hi' h
    have h1 := hT i hi
    have h2 := hT i' hi'
    unfold ap at h1 h2
    rw [h1, h2] at h
    have := congrArg (idx n g⁻¹) h
    rwa [idx_inv_idx, idx_inv_idx] at this


theorem cent5_spec (hn : n < 2 ^ 32) {C : Array Table} {H : Subgroup (Equiv.Perm (Fin n))}
    (hC : EnumsSub n C H) {tT vT : Table} {t : Equiv.Perm (Fin n)} (ht : Rep n tT t)
    (h : cent5OK n C tT vT = true) :
    (∀ z ∈ H, orderOf z = 5 → ∀ c ∈ H, c * z = z * c → ∃ j : ℕ, c = z ^ j ∨ c = t * z ^ j) ∧
    (∀ v : Equiv.Perm (Fin n), Rep n vT v → ∀ z ∈ H, orderOf z = 5 → ∀ c ∈ H,
      v * c * z ≠ z * (v * c)) := by
  have key : ∀ z ∈ H, orderOf z = 5 →
      (∀ c ∈ H, c * z = z * c → ∃ j : ℕ, c = z ^ j ∨ c = t * z ^ j) ∧
      (∀ v : Equiv.Perm (Fin n), Rep n vT v → ∀ c ∈ H, v * c * z ≠ z * (v * c)) := by
    refine hC.forall (p := fun z => !ordTest n 5 z ||
      ((C.all fun c => !commTT n c z || (List.range 5).any fun j =>
          tblEq n c (powT n j z) || tblEq n c (compT n tT (powT n j z))) &&
        C.all fun c => !commTT n (compT n vT c) z)) ?_ h
    intro T z hT hcond hz5
    have hord : ordTest n 5 T = true := (ordTest_iff_perm hT (by norm_num)).2 hz5
    rw [hord] at hcond
    simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true] at hcond
    obtain ⟨hA, hB⟩ := hcond
    refine ⟨fun c hc hcz => ?_, fun v hv c hc => ?_⟩
    · obtain ⟨Tc, -, hTc⟩ := hC.rep_mem hc
      have := hC.forall (p := fun c => !commTT n c T || (List.range 5).any fun j =>
          tblEq n c (powT n j T) || tblEq n c (compT n tT (powT n j T)))
        (P := fun c => c * z = z * c → ∃ j : ℕ, c = z ^ j ∨ c = t * z ^ j) ?_ hA c hc hcz
      · exact this
      · intro Tc' c' hTc' hp hcomm
        have hc1 : commTT n Tc' T = true := (commTT_iff hTc' hT).2 hcomm
        rw [hc1] at hp
        simp only [Bool.not_true, Bool.false_or, List.any_eq_true, List.mem_range,
          Bool.or_eq_true] at hp
        obtain ⟨j, -, hj | hj⟩ := hp
        · exact ⟨j, Or.inl ((tblEq_iff_eq hTc' (Rep.powT hn hT j)).1 hj)⟩
        · exact ⟨j, Or.inr ((tblEq_iff_eq hTc' (Rep.compT ht (Rep.powT hn hT j))).1 hj)⟩
    · have := hC.forall (p := fun c => !commTT n (compT n vT c) T)
        (P := fun c => v * c * z ≠ z * (v * c)) ?_ hB c hc
      · exact this
      · intro Tc' c' hTc' hp hcomm
        have hc1 : commTT n (compT n vT Tc') T = true :=
          (commTT_iff (Rep.compT hv hTc') hT).2 hcomm
        rw [hc1] at hp
        exact Bool.noConfusion hp
  exact ⟨fun z hz h5 => (key z hz h5).1, fun v hv z hz h5 => (key z hz h5).2 v hv⟩


theorem outerComm_spec {P : Subgroup (Equiv.Perm (Fin n))} {pg : Array Table}
    {gg : ℕ → Equiv.Perm (Fin n)} {sift : Table → Bool} (hD : GroupData n P pg gg sift)
    {u : Table} {U : Equiv.Perm (Fin n)} (hu : Rep n u U) (hU2 : U ^ 2 = 1)
    (hUn : ∀ p ∈ P, U * p * U⁻¹ ∈ P) {t v : Table} {tg vg : Equiv.Perm (Fin n)}
    (ht : Rep n t tg) (hv : Rep n v vg) (h : outerCommOK n sift u t v = true) :
    vg ∈ P ⊔ zpowers U ∧ vg ∉ P ∧ orderOf vg = 2 ∧ vg * tg = tg * vg := by
  simp only [outerCommOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hperm, hinv⟩, hsift⟩, hsiftu⟩, hcomm⟩ := h
  refine ⟨mem_R_of_sift hD hU2 hUn hu hv (by rw [hsiftu, Bool.or_true]), ?_,
    orderOf_eq_two_of_involOK hD.lt hv hinv, (commTT_iff hv ht).1 hcomm⟩
  intro hm
  rw [← hD.sift v vg hv, hsift] at hm
  exact Bool.noConfusion hm

theorem derivedIn_spec {D M : Array Table} {H Msub : Subgroup (Equiv.Perm (Fin n))}
    (hD : EnumsSub n D H) (hM : EnumsSub n M Msub) (hinv : invsOK n D = true)
    (h : derivedInOK n D M = true) : ∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ ∈ Msub := by
  intro x hx y hy
  obtain ⟨Tx, hTxD, hTx⟩ := hD.rep_mem hx
  obtain ⟨Ty, hTyD, hTy⟩ := hD.rep_mem hy
  have hix : invOK n Tx (invT n Tx) = true := by
    rw [invsOK, Array.all_eq_true_iff_forall_mem] at hinv
    exact hinv Tx hTxD
  have hiy : invOK n Ty (invT n Ty) = true := by
    rw [invsOK, Array.all_eq_true_iff_forall_mem] at hinv
    exact hinv Ty hTyD
  rw [derivedInOK, Array.all_eq_true_iff_forall_mem] at h
  have h1 := h Tx hTxD
  rw [Array.all_eq_true_iff_forall_mem] at h1
  have h2 := h1 Ty hTyD
  have hrep : Rep n (compT n (compT n Tx Ty) (compT n (invT n Tx) (invT n Ty)))
      (x * y * (x⁻¹ * y⁻¹)) :=
    Rep.compT (Rep.compT hTx hTy) (Rep.compT (Rep.inv_of_invOK hTx hix) (Rep.inv_of_invOK hTy hiy))
  have := (hM.mem_iff hrep).1 h2
  have e : ⁅x, y⁆ = x * y * (x⁻¹ * y⁻¹) := by rw [commutatorElement_def, mul_assoc (x * y)]
  rwa [e]


theorem innerDerived_spec {inner : Table → Bool} {D M : Array Table}
    {H Msub : Subgroup (Equiv.Perm (Fin n))} (hD : EnumsSub n D H) (hM : EnumsSub n M Msub)
    (hinv : invsOK n D = true) (h : innerDerivedOK n inner D M = true)
    {P : Equiv.Perm (Fin n) → Prop} (hPH : ∀ g, P g → g ∈ H)
    (hPin : ∀ g, P g → ∀ T, Rep n T g → inner T = true) :
    ∀ x y, P x → P y → ⁅x, y⁆ ∈ Msub := by
  intro x y hx hy
  obtain ⟨Tx, hTxD, hTx⟩ := hD.rep_mem (hPH x hx)
  obtain ⟨Ty, hTyD, hTy⟩ := hD.rep_mem (hPH y hy)
  have hix : invOK n Tx (invT n Tx) = true := by
    rw [invsOK, Array.all_eq_true_iff_forall_mem] at hinv
    exact hinv Tx hTxD
  have hiy : invOK n Ty (invT n Ty) = true := by
    rw [invsOK, Array.all_eq_true_iff_forall_mem] at hinv
    exact hinv Ty hTyD
  rw [innerDerivedOK, Array.all_eq_true_iff_forall_mem] at h
  have h1 := h Tx hTxD
  rw [hPin x hx Tx hTx] at h1
  simp only [Bool.not_true, Bool.false_or] at h1
  rw [Array.all_eq_true_iff_forall_mem] at h1
  have h2 := h1 Ty hTyD
  rw [hPin y hy Ty hTy] at h2
  simp only [Bool.not_true, Bool.false_or] at h2
  have hrep : Rep n (compT n (compT n Tx Ty) (compT n (invT n Tx) (invT n Ty)))
      (x * y * (x⁻¹ * y⁻¹)) :=
    Rep.compT (Rep.compT hTx hTy) (Rep.compT (Rep.inv_of_invOK hTx hix) (Rep.inv_of_invOK hTy hiy))
  have := (hM.mem_iff hrep).1 h2
  have e : ⁅x, y⁆ = x * y * (x⁻¹ * y⁻¹) := by rw [commutatorElement_def, mul_assoc (x * y)]
  rwa [e]

theorem elemAb_spec (hn : n < 2 ^ 32) {E : Array Table} {H : Subgroup (Equiv.Perm (Fin n))}
    (hE : EnumsSub n E H) (h : elemAbOK n E = true) :
    ∀ x ∈ H, x * x = 1 ∧ ∀ y ∈ H, x * y = y * x := by
  refine hE.forall (p := fun x => tblEq n (compT n x x) (idT n) && E.all fun y => commTT n x y)
    (P := fun x => x * x = 1 ∧ ∀ y ∈ H, x * y = y * x) ?_ h
  intro T x hT hp
  simp only [Bool.and_eq_true] at hp
  obtain ⟨h1, h2⟩ := hp
  refine ⟨(tblEq_iff_eq (Rep.compT hT hT) (Rep.idT hn)).1 h1, fun y hy => ?_⟩
  obtain ⟨Ty, hTyE, hTy⟩ := hE.rep_mem hy
  rw [Array.all_eq_true_iff_forall_mem] at h2
  exact (commTT_iff hT hTy).1 (h2 Ty hTyE)

theorem conjIn_spec {M : Array Table} {Msub : Subgroup (Equiv.Perm (Fin n))} (hM : EnumsSub n M Msub)
    {a b e : Table} {ag bg eg : Equiv.Perm (Fin n)} (ha : Rep n a ag) (hb : Rep n b bg)
    (he : Rep n e eg) (hei : Rep n (invT n e) eg⁻¹) :
    conjInOK n M a b e = true ↔ (eg * ag * eg⁻¹ ∈ Msub ∧ eg * bg * eg⁻¹ ∈ Msub) := by
  rw [conjInOK, Bool.and_eq_true]
  have h1 : Rep n (conjT n e (invT n e) a) (eg * ag * eg⁻¹) :=
    Rep.compT (Rep.compT he ha) hei
  have h2 : Rep n (conjT n e (invT n e) b) (eg * bg * eg⁻¹) :=
    Rep.compT (Rep.compT he hb) hei
  rw [hM.mem_iff h1, hM.mem_iff h2]

theorem mem_normalizer_of_conj_le {G : Type*} [Group G] [Finite G] {M : Subgroup G} {e : G}
    (h : ∀ m ∈ M, e * m * e⁻¹ ∈ M) : e ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h x hx, fun hx => ?_⟩
  have hle : M.map (MulAut.conj e).toMonoidHom ≤ M := by
    rintro _ ⟨m, hm, rfl⟩
    exact h m hm
  have heq : M.map (MulAut.conj e).toMonoidHom = M :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj e).injective])
  have hx' : e * x * e⁻¹ ∈ M.map (MulAut.conj e).toMonoidHom := by rw [heq]; exact hx
  obtain ⟨m, hm, hmx⟩ := hx'
  have : m = x := by
    have h1 : e * m * e⁻¹ = e * x * e⁻¹ := hmx
    simpa using h1
  rw [← this]
  exact hm


theorem card_normCount {Q : CFSG.Certificates.RawSchreierDatum n} (hn : n < 2 ^ 32)
    (hQ : CFSG.Certificates.ValidSchreier Q) {M : Array Table}
    {Msub : Subgroup (Equiv.Perm (Fin n))} (hM : EnumsSub n M Msub) {a b : Table}
    {ag bg : Equiv.Perm (Fin n)} (ha : Rep n a ag) (hb : Rep n b bg) :
    Nat.card {x : Q.originalSubgroup // x * ag * x⁻¹ ∈ Msub ∧ x * bg * x⁻¹ ∈ Msub} =
      normCount n (levelTables Q) M a b := by
  classical
  have hf : ∀ T g, Rep n T g → (normPred n M a b T = true ↔
      (g * ag * g⁻¹ ∈ Msub ∧ g * bg * g⁻¹ ∈ Msub)) := fun T g hT =>
    conjIn_spec hM ha hb hT (rep_invT_of_rep hn hT)
  have h := countProducts_spec (P := fun x : Equiv.Perm (Fin n) =>
    x * ag * x⁻¹ ∈ Msub ∧ x * bg * x⁻¹ ∈ Msub) hf (forall₂_levelTables hn Q)
    (Rep.idT (G := Equiv.Perm (Fin n)) hn)
  simp only [one_mul, List.map_id'] at h
  rw [normCount, h]
  exact card_subtype_eq_countP Q.originalSubgroup (enumeration Q) (enumeration_nodup Q hQ)
    (mem_enumeration_iff Q hQ)
    (fun x : Equiv.Perm (Fin n) => x * ag * x⁻¹ ∈ Msub ∧ x * bg * x⁻¹ ∈ Msub)


end CFSG.GH74.Generic.S45.EvSpor
