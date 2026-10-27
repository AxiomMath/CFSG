module

public import Certificates.Data.Kernel.E6TT.Weyl
public import CFSG.Certificates.Kernel.E6TT.EnumSound
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs

public section

namespace CFSG.KC.E6TT

open CFSG.KC.Enum (strictN strictB)
open Certificates.Data.E6TableT (Vec dot iform cartan roots)
open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Timmesfeld.LangTorus (twistInner)
open CFSG.StandardType.TablePThreeKG (classSet)

local notation "ip" => CFSG.LieType.Steinberg.Adjoint.iform (τ := Tag.E6)

theorem rootReflection_smul_e6
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (v : Fin Tag.E6.rank → ℤ) :
    rootReflection γ • v = v - ip γ v • γ := by
  have h := corootPair_mul hγ v
  obtain ⟨j, hj⟩ := CFSG.LieType.Steinberg.Adjoint.iform_self_of_isRoot hγ
  have h2 : ip γ γ = 2 := by
    rw [hj]
    simp [CFSG.Blueprint.Chevalley.Tag.symmetrizer]
  rw [h2] at h
  have hc : corootPair γ v = ip γ v := by omega
  rw [rootReflection_smul hγ, hc]

theorem pq_dvd
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hroot : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ) {d : ℤ}
    {x : Fin Tag.E6.rank → ℤ} (hx : ∀ γ ∈ Ψ, d ∣ ip γ x) {w : WeylGroup Tag.E6}
    (hw : w ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ Ψ, s = rootReflection γ}) :
    ∀ (e : ℤ) (z : Fin Tag.E6.rank → ℤ), (∀ γ ∈ Ψ, e ∣ ip γ z) → d * e ∣ ip (w • x - x) z := by
  have step : ∀ γ ∈ Ψ, ∀ u : WeylGroup Tag.E6,
      (∀ (e : ℤ) (z : Fin Tag.E6.rank → ℤ), (∀ γ ∈ Ψ, e ∣ ip γ z) → d * e ∣ ip (u • x - x) z) →
      ∀ (e : ℤ) (z : Fin Tag.E6.rank → ℤ), (∀ γ ∈ Ψ, e ∣ ip γ z) →
        d * e ∣ ip ((rootReflection γ * u) • x - x) z := by
    intro γ hγ u ih e z hz
    have hA : d ∣ ip γ (u • x - x) := by
      have := ih 1 γ (fun _ _ => one_dvd _)
      rw [mul_one, CFSG.LieType.Steinberg.Adjoint.iform_comm] at this
      exact this
    have e1 : (rootReflection γ * u) • x - x = (u • x - x) - ip γ (u • x) • γ := by
      rw [mul_smul, rootReflection_smul_e6 (hroot γ hγ)]
      abel
    have e2 : ip γ (u • x) = ip γ (u • x - x) + ip γ x := by
      rw [CFSG.LieType.Steinberg.Adjoint.iform_sub_right]
      ring
    rw [e1, CFSG.LieType.Steinberg.Adjoint.iform_sub_left,
      CFSG.LieType.Steinberg.Adjoint.iform_smul_left, e2]
    exact dvd_sub (ih e z hz) (mul_dvd_mul (dvd_add hA (hx γ hγ)) (hz γ hγ))
  refine Subgroup.closure_induction_left
    (p := fun u _ => ∀ (e : ℤ) (z : Fin Tag.E6.rank → ℤ), (∀ γ ∈ Ψ, e ∣ ip γ z) →
      d * e ∣ ip (u • x - x) z) ?_ ?_ ?_ hw
  · intro e z _
    simp [CFSG.LieType.Steinberg.Adjoint.iform]
  · rintro _ ⟨γ, hγ, rfl⟩ u _ ih
    exact step γ hγ u ih
  · rintro _ ⟨γ, hγ, rfl⟩ u _ ih
    rw [rootReflection_inv (hroot γ hγ)]
    exact step γ hγ u ih

theorem eq_of_mem_closure {σ τ' : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)}
    (hσ : ∀ a b, σ (a + b) = σ a + σ b) (hτ : ∀ a b, τ' (a + b) = τ' a + τ' b)
    {S : Set (Fin Tag.E6.rank → ℤ)} (h : ∀ s ∈ S, σ s = τ' s) {x : Fin Tag.E6.rank → ℤ}
    (hx : x ∈ AddSubgroup.closure S) : σ x = τ' x := by
  let φ : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) := AddMonoidHom.mk' σ hσ
  let ψ : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) := AddMonoidHom.mk' τ' hτ
  exact AddMonoidHom.eqOn_closure (f := φ) (g := ψ) h hx

theorem twistInner_pq_dvd
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hroot : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ)
    {σ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hadd : ∀ a b, σ (a + b) = σ a + σ b)
    (ht : twistInner Ψ σ) {d : ℤ} {x y : Fin Tag.E6.rank → ℤ} (hxΨ : x ∈ AddSubgroup.closure Ψ)
    (hx : ∀ γ ∈ Ψ, d ∣ ip γ x) (hy : ∀ γ ∈ Ψ, d ∣ ip γ y) : d * d ∣ ip (σ x - x) y := by
  obtain ⟨w, hw, hσw⟩ := ht
  have e : σ x = w • x := eq_of_mem_closure hadd (fun a b => smul_add w a b) hσw hxΨ
  rw [e]
  exact pq_dvd hroot hx hw d y hy

@[expose] def toV (x : Vec) : Fin Tag.E6.rank → ℤ := fun i => x.getD i.val 0

theorem toV_ofFn (γ : Fin Tag.E6.rank → ℤ) : toV (List.ofFn γ) = γ := by
  funext i
  fin_cases i <;> rfl

theorem length_ofFn6 (γ : Fin Tag.E6.rank → ℤ) : (List.ofFn γ).length = 6 := List.length_ofFn

theorem eq_six {x : Vec} (hx : x.length = 6) :
    ∃ a0 a1 a2 a3 a4 a5 : ℤ, x = [a0, a1, a2, a3, a4, a5] := by
  match x, hx with
  | [a0, a1, a2, a3, a4, a5], _ => exact ⟨a0, a1, a2, a3, a4, a5, rfl⟩

theorem ofFn_toV {x : Vec} (hx : x.length = 6) : List.ofFn (toV x) = x := by
  obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ := eq_six hx
  rfl

theorem toV_injective {x y : Vec} (hx : x.length = 6) (hy : y.length = 6) (h : toV x = toV y) :
    x = y := by
  rw [← ofFn_toV hx, ← ofFn_toV hy, h]

theorem length_digs (w off : Nat) : ∀ (n K : Nat), (digs w off K n).length = n
  | 0, _ => rfl
  | n + 1, K => by
    change (_ :: digs w off (Nat.shiftRight K w) n).length = n + 1
    rw [List.length_cons, length_digs w off n]

theorem length_vecs : ∀ (r K : Nat), (vecs K r).length = r
  | 0, _ => rfl
  | r + 1, K => by
    change (_ :: vecs (Nat.shiftRight K 18) r).length = r + 1
    rw [List.length_cons, length_vecs r]

theorem length_of_mem_vecs : ∀ (r K : Nat), ∀ v ∈ vecs K r, v.length = 6
  | 0, _, v, h => absurd h List.not_mem_nil
  | r + 1, K, v, h => by
    change v ∈ _ :: vecs (Nat.shiftRight K 18) r at h
    rcases List.mem_cons.1 h with rfl | h
    · exact length_digs _ _ _ _
    · exact length_of_mem_vecs r _ v h

theorem length_vsc (c : ℤ) {x y : Vec} (hx : x.length = 6) (hy : y.length = 6) :
    (vsc c x y).length = 6 := by
  simp [vsc, hx, hy]

theorem toV_vsc (c : ℤ) {x y : Vec} (hx : x.length = 6) (hy : y.length = 6) :
    toV (vsc c x y) = toV x + c • toV y := by
  obtain ⟨a0, a1, a2, a3, a4, a5, rfl⟩ := eq_six hx
  obtain ⟨b0, b1, b2, b3, b4, b5, rfl⟩ := eq_six hy
  funext i
  fin_cases i <;> simp [toV, vsc, Int.add_def, Int.mul_def]

theorem lin_cons_cons (c : ℤ) (cs : List ℤ) (δ : Vec) (Δ : List Vec) :
    lin (c :: cs) (δ :: Δ) = vsc c (lin cs Δ) δ := rfl

theorem lin_mem (S : Set (Fin Tag.E6.rank → ℤ)) : ∀ (cs : List ℤ) (Δ : List Vec),
    (∀ δ ∈ Δ, δ.length = 6) → (∀ δ ∈ Δ, toV δ ∈ S) →
      (lin cs Δ).length = 6 ∧ toV (lin cs Δ) ∈ AddSubgroup.closure S
  | [], Δ, _, _ => ⟨rfl, by
      have : toV z6 = 0 := by funext i; fin_cases i <;> rfl
      change toV z6 ∈ _
      rw [this]
      exact zero_mem _⟩
  | c :: cs, [], _, _ => ⟨rfl, by
      have : toV z6 = 0 := by funext i; fin_cases i <;> rfl
      change toV z6 ∈ _
      rw [this]
      exact zero_mem _⟩
  | c :: cs, δ :: Δ, h6, hS => by
    obtain ⟨hl, hm⟩ := lin_mem S cs Δ (fun δ' h => h6 δ' (List.mem_cons_of_mem _ h))
      (fun δ' h => hS δ' (List.mem_cons_of_mem _ h))
    have hδ := h6 δ List.mem_cons_self
    rw [lin_cons_cons]
    refine ⟨length_vsc c hl hδ, ?_⟩
    rw [toV_vsc c hl hδ]
    exact add_mem hm (AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (hS δ List.mem_cons_self)) c)

theorem iform_eq_ip {x y : Vec} (hx : x.length = 6) (hy : y.length = 6) :
    iform x y = ip (toV x) (toV y) := by
  rw [← checker_iform_ofFnE, ofFn_toV hx, ofFn_toV hy]

theorem mem_classSet_toV {l : List Vec} {x : Vec} (hx : x.length = 6) (h : x ∈ l) :
    toV x ∈ classSet l := by
  change List.ofFn (toV x) ∈ l
  rw [ofFn_toV hx]
  exact h

theorem isRoot_of_mem_classSet {l : List Vec} (hroot : ∀ x ∈ l, x ∈ roots ())
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ classSet l) : IsRoot Tag.E6 γ :=
  (CFSG.StandardType.TablePThreeKG.isRoot_iff_mem_roots γ).2 (hroot _ hγ)

theorem beq_true_eq {α : Type} [BEq α] [LawfulBEq α] {a b : α} (h : (a == b) = true) : a = b :=
  beq_iff_eq.1 h

theorem omOK_spec {l Δ : List Vec} {r : Nat} {d : ℤ} {o : List Nat} (h : omOK l Δ r d o = true) :
    digs 8 128 (o.getD 0 0) 6 = lin (digs 8 128 (o.getD 1 0) r) Δ ∧
      digs 8 128 (o.getD 2 0) 6 = cartan.map (dot (digs 8 128 (o.getD 0 0) 6)) ∧
      ∀ x ∈ l, d ∣ dot x (digs 8 128 (o.getD 2 0) 6) := by
  obtain ⟨h1, h2⟩ := bAnd_true h
  obtain ⟨h2, h3⟩ := bAnd_true h2
  refine ⟨beq_true_eq h1, beq_true_eq h2, fun x hx => ?_⟩
  have := List.all_eq_true.1 h3 x hx
  exact Int.dvd_of_emod_eq_zero (beq_true_eq this)

theorem classK_spec {l : List Vec} {H : List Nat} {O : List (List Nat)}
    (h : classK l H O = true) :
    (∀ δ ∈ vecs (H.getD 2 0) (H.getD 0 0), δ ∈ l) ∧
      (∀ x ∈ l, ∃ cs, x = lin cs (vecs (H.getD 2 0) (H.getD 0 0))) ∧
      (∀ o ∈ O, omOK l (vecs (H.getD 2 0) (H.getD 0 0)) (H.getD 0 0) (Int.ofNat (H.getD 1 0)) o =
        true) ∧
      tabOK (vecs (H.getD 2 0) (H.getD 0 0)) (H.getD 0 0) (H.getD 3 0) (H.getD 4 0) (H.getD 5 0) =
        true := by
  obtain ⟨h1, h2⟩ := bAnd_true h
  obtain ⟨h2, h3⟩ := bAnd_true h2
  obtain ⟨h3, h4⟩ := bAnd_true h3
  refine ⟨fun δ hδ => List.contains_iff_mem.1 (List.all_eq_true.1 h1 δ hδ), fun x hx => ?_,
    List.all_eq_true.1 h3, h4⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := allIdx_spec _ l 0 h2 j hj
  rw [List.getD_eq_getElem _ _ hj] at this
  exact ⟨_, beq_true_eq this⟩

theorem wOKK_spec : ∀ {cl : List (List Vec)} {Hs : List (List Nat)} {Os : List (List (List Nat))},
    wOKK cl Hs Os = true → Hs.length = cl.length ∧ Os.length = cl.length ∧
      ∀ j < cl.length, classK (cl.getD j []) (Hs.getD j []) (Os.getD j []) = true
  | [], Hs, Os, h => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, fun j hj => absurd hj (by simp)⟩
  | l :: cl, [], Os, h => absurd h (by simp [wOKK])
  | l :: cl, H :: Hs, [], h => absurd h (by simp [wOKK])
  | l :: cl, H :: Hs, O :: Os, h => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    obtain ⟨e1, e2, e3⟩ := wOKK_spec h2
    refine ⟨by simp [e1], by simp [e2], fun j hj => ?_⟩
    rcases j with _ | j
    · exact h1
    · exact e3 j (by simpa using hj)

theorem vsc_refl
    {δs δ : Vec} (hs : δs.length = 6) (hδ : δ.length = 6) (hroot : IsRoot Tag.E6 (toV δs))
    (w : WeylGroup Tag.E6) :
    vsc (Int.neg (iform δs δ)) (List.ofFn (w • toV δ)) (List.ofFn (w • toV δs)) =
      List.ofFn ((w * rootReflection (toV δs)) • toV δ) := by
  apply toV_injective (length_vsc _ (length_ofFn6 _) (length_ofFn6 _)) (length_ofFn6 _)
  rw [toV_vsc _ (length_ofFn6 _) (length_ofFn6 _), toV_ofFn, toV_ofFn, toV_ofFn, mul_smul,
    rootReflection_smul_e6 hroot, smul_sub, smul_comm, iform_eq_ip hs hδ]
  have hn : Int.neg (ip (toV δs) (toV δ)) = -ip (toV δs) (toV δ) := rfl
  rw [hn, neg_smul, smul_neg, sub_eq_add_neg]

theorem tab_sound {l : List Vec}
    (hroot : ∀ x ∈ l, x ∈ roots ()) {Δ : List Vec} {r TK TM n : Nat}
    (hΔl : ∀ δ ∈ Δ, δ ∈ l)
    (hΔ6 : ∀ δ ∈ Δ, δ.length = 6) (hr : Δ.length = r) (h : tabOK Δ r TK TM n = true) :
    ∀ e < n, ∃ w ∈ Subgroup.closure {s : WeylGroup Tag.E6 | ∃ γ ∈ classSet l, s = rootReflection γ},
      vecs (keyAt TK r e) r = Δ.map fun δ => List.ofFn (w • toV δ) := by
  have hall : ∀ e < n, tabEntry Δ r TK TM n e = true := fun e he =>
    allBelow_specE h e he (by
      change e < 64 * (n >>> 6 + 1)
      rw [Nat.shiftRight_eq_div_pow]
      omega)
  let dep : Nat → Nat := fun e => Nat.land fld(TM, Nat.mul 24 e, 16777215) 31
  suffices H : ∀ m, ∀ e < n, dep e = m → ∃ w ∈ Subgroup.closure {s : WeylGroup Tag.E6 |
      ∃ γ ∈ classSet l, s = rootReflection γ},
      vecs (keyAt TK r e) r = Δ.map fun δ => List.ofFn (w • toV δ) from
    fun e he => H _ e he rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro e he hm
  have hE := hall e he
  simp only [tabEntry, strictB_eqE] at hE
  by_cases h0 : Nat.beq (Nat.land fld(TM, Nat.mul 24 e, 16777215) 31) 0 = true
  · rw [h0] at hE
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [beq_true_eq hE]
    conv_lhs => rw [← List.map_id Δ]
    apply List.map_congr_left
    intro δ hδ
    rw [one_smul, ofFn_toV (hΔ6 δ hδ)]
    rfl
  · rw [Bool.not_eq_true] at h0
    rw [h0] at hE
    obtain ⟨hp, hE⟩ := bAnd_true hE
    obtain ⟨hs, hE⟩ := bAnd_true hE
    obtain ⟨hd, hE⟩ := bAnd_true hE
    rw [Nat.blt_eq] at hp hs
    have hp' := hp
    have hs' := hs
    have hd' := Nat.eq_of_beq_eq_true hd
    have h0' : Nat.land fld(TM, Nat.mul 24 e, 16777215) 31 ≠ 0 := fun h => by
      rw [h] at h0
      exact absurd h0 (by decide)
    have hdp : dep (Nat.shiftRight fld(TM, Nat.mul 24 e, 16777215) 8) + 1 = dep e := hd'
    obtain ⟨w, hw, hwX⟩ := ih (dep (Nat.shiftRight fld(TM, Nat.mul 24 e, 16777215) 8))
      (by omega) _ hp' rfl
    have hsΔ : Nat.land (Nat.shiftRight fld(TM, Nat.mul 24 e, 16777215) 5) 7 < Δ.length :=
      hr ▸ hs'
    set s := Nat.land (Nat.shiftRight fld(TM, Nat.mul 24 e, 16777215) 5) 7 with hs_def
    have hδs : Δ.getD s [] ∈ Δ := by
      rw [List.getD_eq_getElem _ _ hsΔ]
      exact List.getElem_mem hsΔ
    have h6s := hΔ6 _ hδs
    have hrs : IsRoot Tag.E6 (toV (Δ.getD s [])) :=
      isRoot_of_mem_classSet hroot (mem_classSet_toV h6s (hΔl _ hδs))
    refine ⟨w * rootReflection (toV (Δ.getD s [])),
      Subgroup.mul_mem _ hw (Subgroup.subset_closure
        ⟨_, mem_classSet_toV h6s (hΔl _ hδs), rfl⟩), ?_⟩
    rw [beq_true_eq hE, hwX]
    unfold rstep grow
    have hg : (List.map (fun δ => List.ofFn (w • toV δ)) Δ).getD s [] =
        List.ofFn (w • toV (Δ.getD s [])) := by
      rw [List.getD_eq_getElem _ _ (by simpa using hsΔ), List.getElem_map,
        List.getD_eq_getElem _ _ hsΔ]
    rw [hg, List.zipWith_map, List.zipWith_self]
    apply List.map_congr_left
    intro δ hδ
    exact vsc_refl h6s (hΔ6 δ hδ) hrs w

theorem inK_sound {l : List Vec}
    (hroot : ∀ x ∈ l, x ∈ roots ()) {H : List Nat} {O : List (List Nat)} (hc : classK l H O = true)
    {σ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hadd : ∀ a b, σ (a + b) = σ a + σ b)
    {f : Vec → Vec} (hf : ∀ γ, f (List.ofFn γ) = List.ofFn (σ γ)) (hin : inK H f = true) :
    twistInner (classSet l) σ := by
  obtain ⟨hΔl, hlin, -, htab⟩ := classK_spec hc
  set Δ := vecs (H.getD 2 0) (H.getD 0 0) with hΔdef
  have hΔ6 : ∀ δ ∈ Δ, δ.length = 6 := length_of_mem_vecs _ _
  simp only [inK, strictB_eqE] at hin
  obtain ⟨hi, heq⟩ := bAnd_true hin
  rw [Nat.blt_eq] at hi
  obtain ⟨w, hw, hwX⟩ := tab_sound hroot hΔl hΔ6 (length_vecs _ _) htab _ hi
  rw [hwX] at heq
  have hagree : ∀ δ ∈ Δ, σ (toV δ) = w • toV δ := by
    intro δ hδ
    have h1 := beq_true_eq heq
    have h2 : (Δ.map fun δ => List.ofFn (w • toV δ)).getD (Δ.idxOf δ) [] =
        (Δ.map f).getD (Δ.idxOf δ) [] := by rw [h1]
    have hlt : Δ.idxOf δ < Δ.length := List.idxOf_lt_length_of_mem hδ
    have hlt' : Δ.idxOf δ < (Δ.map f).length := by rw [List.length_map]; exact hlt
    have hlt'' : Δ.idxOf δ < (Δ.map fun δ => List.ofFn (w • toV δ)).length := by
      rw [List.length_map]; exact hlt
    rw [List.getD_eq_getElem _ _ hlt', List.getD_eq_getElem _ _ hlt'', List.getElem_map,
      List.getElem_map, List.getElem_idxOf] at h2
    have h3 : f δ = List.ofFn (σ (toV δ)) := by rw [← hf, ofFn_toV (hΔ6 δ hδ)]
    rw [h3] at h2
    exact (List.ofFn_injective h2).symm
  refine ⟨w, hw, fun γ hγ => ?_⟩
  obtain ⟨cs, hcs⟩ := hlin _ hγ
  have hmem := (lin_mem (toV '' {δ | δ ∈ Δ}) cs Δ hΔ6 (fun δ hδ => ⟨δ, hδ, rfl⟩)).2
  rw [← hcs, toV_ofFn] at hmem
  refine eq_of_mem_closure hadd (fun a b => smul_add w a b) ?_ hmem
  rintro _ ⟨δ, hδ, rfl⟩
  exact hagree δ hδ

theorem outK_sound {l : List Vec}
    (hroot : ∀ x ∈ l, x ∈ roots ()) {H : List Nat} {O : List (List Nat)} (hc : classK l H O = true)
    {σ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ)} (hadd : ∀ a b, σ (a + b) = σ a + σ b)
    {f : Vec → Vec} (hf : ∀ γ, f (List.ofFn γ) = List.ofFn (σ γ)) (hout : outK H O f = true) :
    ¬ twistInner (classSet l) σ := by
  intro ht
  obtain ⟨hΔl, -, hom, -⟩ := classK_spec hc
  set Δ := vecs (H.getD 2 0) (H.getD 0 0) with hΔdef
  have hΔ6 : ∀ δ ∈ Δ, δ.length = 6 := length_of_mem_vecs _ _
  have hrootΨ : ∀ γ ∈ classSet l, IsRoot Tag.E6 γ := fun γ hγ => isRoot_of_mem_classSet hroot hγ
  set d : ℤ := Int.ofNat (H.getD 1 0) with hd
  have gen : ∀ o ∈ O, (digs 8 128 (o.getD 0 0) 6).length = 6 ∧
      toV (digs 8 128 (o.getD 0 0) 6) ∈ AddSubgroup.closure (classSet l) ∧
      (∀ γ ∈ classSet l, d ∣ ip γ (toV (digs 8 128 (o.getD 0 0) 6))) ∧
      ∀ x : Vec, dot x (digs 8 128 (o.getD 2 0) 6) = iform x (digs 8 128 (o.getD 0 0) 6) := by
    intro o ho
    obtain ⟨e1, e2, e3⟩ := omOK_spec (hom o ho)
    have hW := lin_mem (classSet l) (digs 8 128 (o.getD 1 0) (H.getD 0 0)) Δ hΔ6
      (fun δ hδ => mem_classSet_toV (hΔ6 δ hδ) (hΔl δ hδ))
    rw [← e1] at hW
    refine ⟨hW.1, hW.2, fun γ hγ => ?_, fun x => by rw [e2]; rfl⟩
    have h1 : dot (List.ofFn γ) (digs 8 128 (o.getD 2 0) 6) =
        ip γ (toV (digs 8 128 (o.getD 0 0) 6)) := by
      rw [e2]
      change iform (List.ofFn γ) _ = _
      rw [iform_eq_ip (length_ofFn6 γ) hW.1, toV_ofFn]
    rw [← h1]
    exact e3 _ hγ
  simp only [outK, List.any_eq_true] at hout
  obtain ⟨o, ho, o', ho', hne⟩ := hout
  obtain ⟨h6, hcl, hdv, -⟩ := gen o ho
  obtain ⟨h6', -, hdv', hU'⟩ := gen o' ho'
  rw [← hd] at hne
  set W := digs 8 128 (o.getD 0 0) 6
  set W' := digs 8 128 (o'.getD 0 0) 6
  have key := twistInner_pq_dvd hrootΨ hadd ht hcl hdv hdv'
  have hfW : f W = List.ofFn (σ (toV W)) := by rw [← hf, ofFn_toV h6]
  rw [hU', hU', hfW, iform_eq_ip (length_ofFn6 _) h6', iform_eq_ip h6 h6', toV_ofFn] at hne
  have hz : Int.emod (Int.sub (ip (σ (toV W)) (toV W')) (ip (toV W) (toV W'))) (Int.mul d d) = 0 := by
    have e : Int.sub (ip (σ (toV W)) (toV W')) (ip (toV W) (toV W')) =
        ip (σ (toV W) - toV W) (toV W') := by
      rw [CFSG.LieType.Steinberg.Adjoint.iform_sub_left]
      rfl
    rw [e]
    exact Int.emod_eq_zero_of_dvd key
  rw [hz] at hne
  exact absurd hne (by decide)

end CFSG.KC.E6TT

end
