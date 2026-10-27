module

public import CFSG.Certificates.Kernel.D43.FrobSound
public import Certificates.Data.Kernel.D43.Conj

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.F3.Native CFSG.Sporadic.Fi23.Native
  CFSG.Sporadic.ON.Native CFSG.ASVolI CFSG.Blueprint.Chevalley CFSG.LieType.Ree


variable {K : Type} [Field K]

@[expose] noncomputable def evE (ω : K) (w : List ℕ) (v : RootModule .D4 K) : RootModule .D4 K :=
  w.foldr (fun i v => burnsideF48d_genEnd ω i v) v

@[expose] noncomputable def evH (ω : K) : List ℕ → RootModule .D4 K →+ RootModule .D4 K
  | [] => AddMonoidHom.id _
  | i :: w => (burnsideF48d_genEnd ω i).toAddMonoidHom.comp (evH ω w)

theorem evH_apply (ω : K) : ∀ (w : List ℕ) (v : RootModule .D4 K), evH ω w v = evE ω w v
  | [], _ => rfl
  | i :: w, v => by
    change burnsideF48d_genEnd ω i (evH ω w v) = burnsideF48d_genEnd ω i (evE ω w v)
    rw [evH_apply ω w v]

variable [CharP K 3] (ω : K) (hω : ω ^ 3 = ω + 1)

include hω in
theorem Ψ_mv_gen {RL : List (List Nat)} {k : Nat} (hr : rowsOK (RL.getD k []) k = true)
    (hk : k < 8) {X : Nat} (hX : wf84 X = true) :
    burnsideF48d_Ψ ω (vecOf (ofV (vOf (mv (RL.getD k []) X)))) =
      burnsideF48d_genEnd ω k (burnsideF48d_Ψ ω (vecOf (ofV (vOf X)))) := by
  rw [← rows_mulVecT hr (wf84_spec hX).1]
  have hrk : burnsideF48d_rows (burnsideF48d_colTab ()) k =
      burnsideF48d_genRows (burnsideF48d_colTab ()) k := if_neg (by omega)
  rw [hrk]
  exact burnsideF48d_Ψ_combW ω (burnsideF48d_rowsWF _)
    (wf_of_canon154 (canon154_vOf (wf84_spec hX).2.1)) _ (burnsideF48d_Ψ_genRows ω hω k)

include hω in
theorem Ψ_mv_frob {RL : List (List Nat)} (hr : rowsOK (RL.getD 8 []) 8 = true) {X : Nat}
    (hX : wf84 X = true) :
    burnsideF48d_Ψ ω (vecOf (ofV (vOf (mv (RL.getD 8 []) X)))) =
      frobV (burnsideF48d_Ψ ω (vecOf (ofV (vOf X)))) := by
  rw [← rows_mulVecT hr (wf84_spec hX).1]
  have hrk : burnsideF48d_rows (burnsideF48d_colTab ()) 8 = burnsideF48d_frobRows () := if_pos rfl
  rw [hrk]
  exact Ψ_combW_frob ω hω (wf_of_canon154 (canon154_vOf (wf84_spec hX).2.1))

theorem wf84_mvW {RL : List (List Nat)} : ∀ {w : List Nat} {X : Nat}, mvWok RL w X = true →
    wf84 (mvW RL w X) = true
  | [], _, h => h
  | _ :: _, _, h => by
    simp only [mvWok, Bool.and_eq_true] at h
    exact h.2

include hω in
theorem Ψ_mvW {RL : List (List Nat)} (hrows : ∀ k < 8, rowsOK (RL.getD k []) k = true) :
    ∀ (w : List Nat), (∀ i ∈ w, i < 8) → ∀ X, mvWok RL w X = true →
      burnsideF48d_Ψ ω (vecOf (ofV (vOf (mvW RL w X)))) =
        evE ω w (burnsideF48d_Ψ ω (vecOf (ofV (vOf X))))
  | [], _, _, _ => rfl
  | k :: w, hw, X, h => by
    have h' := h
    simp only [mvWok, Bool.and_eq_true] at h'
    have hk : k < 8 := hw k (List.mem_cons_self ..)
    change burnsideF48d_Ψ ω (vecOf (ofV (vOf (mv (RL.getD k []) (mvW RL w X))))) =
      burnsideF48d_genEnd ω k (evE ω w (burnsideF48d_Ψ ω (vecOf (ofV (vOf X)))))
    rw [Ψ_mv_gen ω hω (hrows k hk) hk (wf84_mvW h'.1),
      Ψ_mvW hrows w (fun i hi => hw i (List.mem_cons_of_mem _ hi)) X h'.1]

variable (hK : Nat.card K = 27)

include hK hω in
theorem φ_surj (c : K) : ∃ n < 27, burnsideF48d_φ ω n = c := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  have hinj : Set.InjOn (burnsideF48d_φ ω) (Finset.range 27 : Set ℕ) := fun a ha b hb h =>
    burnsideF48d_φ_injOn ω hω (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h
  have hcard : ((Finset.range 27).image (burnsideF48d_φ ω)).card = Fintype.card K := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, ← Nat.card_eq_fintype_card, hK]
  have hall : (Finset.range 27).image (burnsideF48d_φ ω) = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  have hc : c ∈ (Finset.range 27).image (burnsideF48d_φ ω) := by rw [hall]; exact Finset.mem_univ c
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hc
  exact ⟨n, Finset.mem_range.1 hn, rfl⟩

include hK hω in
theorem addHom_ext_b {f g : RootModule .D4 K →+ RootModule .D4 K}
    (h : ∀ q < 84, f (burnsideF48d_b ω q) = g (burnsideF48d_b ω q)) : f = g := by
  refine Finsupp.addHom_ext fun a c => ?_
  obtain ⟨i, rfl⟩ := CFSG.LieType.Ree.surjective_toLabel burnsideF48d_hC a
  obtain ⟨n, -, rfl⟩ := φ_surj ω hω hK c
  set l := burnsideF48d_ofIdx i with hl
  have hl28 : l < 28 := burnsideF48d_ofIdx_lt i
  have hi : i = burnsideF48d_idx l := (burnsideF48d_idx_ofIdx i).symm
  have hb : ∀ j < 3, Finsupp.single (toLabel burnsideF48d_hC i) (ω ^ j) =
      burnsideF48d_b ω (3 * l + j) := by
    intro j hj
    rw [burnsideF48d_b, if_pos (by omega), show (3 * l + j) % 3 = j by omega,
      show (3 * l + j) / 3 = l by omega, burnsideF48d_e, ← hi, Finsupp.smul_single, smul_eq_mul,
      mul_one]
  have hs : ∀ (m : ℕ) (x : K), Finsupp.single (toLabel burnsideF48d_hC i) ((m : K) * x) =
      m • Finsupp.single (toLabel burnsideF48d_hC i) x := fun m x => by
    rw [Finsupp.smul_single, nsmul_eq_mul]
  have e : Finsupp.single (toLabel burnsideF48d_hC i) (burnsideF48d_φ ω n) =
      (n % 3) • burnsideF48d_b ω (3 * l + 0) +
        (n / 3 % 3) • burnsideF48d_b ω (3 * l + 1) +
          (n / 9 % 3) • burnsideF48d_b ω (3 * l + 2) := by
    rw [burnsideF48d_φ, ← hb 0 (by norm_num), ← hb 1 (by norm_num), ← hb 2 (by norm_num), ← hs,
      ← hs, ← hs, ← Finsupp.single_add, ← Finsupp.single_add]
    congr 1
    ring
  rw [e, map_add, map_add, map_add, map_add, map_nsmul, map_nsmul, map_nsmul, map_nsmul,
    map_nsmul, map_nsmul, h (3 * l + 0) (by omega), h (3 * l + 1) (by omega),
    h (3 * l + 2) (by omega)]

include hω in
theorem frob_genEnd_b {RL : List (List Nat)} (hrows : ∀ k < 9, rowsOK (RL.getD k []) k = true)
    {k : Nat} (hk : k < 8) {w : List Nat} (hw : ∀ i ∈ w, i < 8) (h : conjOK RL k w = true)
    {q : ℕ} (hq : q < 84) :
    frobV (burnsideF48d_genEnd ω k (burnsideF48d_b ω q)) = evE ω w (frobV (burnsideF48d_b ω q)) := by
  have hj := List.all_eq_true.1 h q (List.mem_range.2 hq)
  simp only [Bool.and_eq_true] at hj
  obtain ⟨⟨ha, hc⟩, he⟩ := hj
  have hgk : burnsideF48d_rows (burnsideF48d_colTab ()) k =
      burnsideF48d_genRows (burnsideF48d_colTab ()) k := if_neg (by omega)
  have h8 : burnsideF48d_rows (burnsideF48d_colTab ()) 8 = burnsideF48d_frobRows () := if_pos rfl
  have g1 : burnsideF48d_Ψ ω (vecOf (burnsideF48d_genRows (burnsideF48d_colTab ()) k)[q]!) =
      burnsideF48d_genEnd ω k (burnsideF48d_b ω q) :=
    burnsideF48d_Ψ_genRows ω hω k ⟨q, by omega⟩
  have g2 : burnsideF48d_Ψ ω (vecOf (burnsideF48d_frobRows ())[q]!) =
      frobV (burnsideF48d_b ω q) := Ψ_frobRows ω hω ⟨q, by omega⟩
  have e1 : burnsideF48d_genEnd ω k (burnsideF48d_b ω q) =
      burnsideF48d_Ψ ω (vecOf (ofV (vOf ((RL.getD k []).getD q 0)))) := by
    rw [← g1, ← hgk, ((rowsOK_spec (hrows k (by omega))).2 q hq).1]
  have e2 : frobV (burnsideF48d_b ω q) =
      burnsideF48d_Ψ ω (vecOf (ofV (vOf ((RL.getD 8 []).getD q 0)))) := by
    rw [← g2, ← h8, ((rowsOK_spec (hrows 8 (by omega))).2 q hq).1]
  rw [e1, e2, ← Ψ_mv_frob ω hω (hrows 8 (by omega)) ha, Nat.eq_of_beq_eq_true he,
    Ψ_mvW ω hω (fun k hk => hrows k (by omega)) w hw _ hc]

include hK hω in
theorem frob_genEnd_of_conjOK {RL : List (List Nat)}
    (hrows : ∀ k < 9, rowsOK (RL.getD k []) k = true) {k : Nat} (hk : k < 8) {w : List Nat}
    (hw : ∀ i ∈ w, i < 8) (h : conjOK RL k w = true) (v : RootModule .D4 K) :
    frobV (burnsideF48d_genEnd ω k v) = evE ω w (frobV v) := by
  have e := addHom_ext_b ω hω hK (f := frobH.comp (burnsideF48d_genEnd ω k).toAddMonoidHom)
    (g := (evH ω w).comp frobH) fun q hq => by
      change frobV (burnsideF48d_genEnd ω k (burnsideF48d_b ω q)) =
        evH ω w (frobV (burnsideF48d_b ω q))
      rw [evH_apply]
      exact frob_genEnd_b ω hω hrows hk hw h hq
  have := congrArg (fun f => f v) e
  change frobV (burnsideF48d_genEnd ω k v) = evH ω w (frobV v) at this
  rw [this, evH_apply]

omit [CharP K 3] in
include hK in
theorem frobV_cube (v : RootModule .D4 K) : frobV (frobV (frobV v)) = v := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 27 := by rw [← Nat.card_eq_fintype_card, hK]
  ext l
  rw [frobV_apply, frobV_apply, frobV_apply, ← pow_mul, ← pow_mul,
    show 3 * 3 * 3 = Fintype.card K by rw [hc], FiniteField.pow_card]

omit [CharP K 3] in
@[expose] noncomputable def glPerm (u : ModGL Tag.D4 K) : ↥(negPerm K) :=
  ⟨{ toFun := fun v => (u : Module.End K (RootModule Tag.D4 K)) v
     invFun := fun v => ((u⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) v
     left_inv := fun v => by
       change ((u⁻¹ * u : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) v = v
       rw [inv_mul_cancel]
       rfl
     right_inv := fun v => by
       change ((u * u⁻¹ : ModGL Tag.D4 K) : Module.End K (RootModule Tag.D4 K)) v = v
       rw [mul_inv_cancel]
       rfl }, fun v => by
    change (u : Module.End K (RootModule Tag.D4 K)) (-v) = -(u : Module.End K (RootModule Tag.D4 K)) v
    exact map_neg _ v⟩

omit [CharP K 3] in
theorem glPerm_apply (u : ModGL Tag.D4 K) (v : RootModule .D4 K) :
    ((glPerm u : ↥(negPerm K)) : Equiv.Perm (RootModule Tag.D4 K)) v =
      (u : Module.End K (RootModule Tag.D4 K)) v := rfl

@[expose] noncomputable def frobPerm : ↥(negPerm K) :=
  ⟨{ toFun := frobV
     invFun := fun v => frobV (frobV v)
     left_inv := fun v => frobV_cube hK v
     right_inv := fun v => frobV_cube hK v }, fun v => by
      change frobV (-v) = -frobV v
      rw [← frobH_apply, map_neg]
      rfl⟩

theorem frobPerm_apply (v : RootModule .D4 K) :
    ((frobPerm hK : ↥(negPerm K)) : Equiv.Perm (RootModule Tag.D4 K)) v = frobV v := rfl

end CFSG.KC.D43

end
