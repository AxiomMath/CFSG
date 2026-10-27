
module

public import CFSG.Certificates.Kernel.Misc.WordPtsSound
public import CFSG.Quasithin.Vol2.KGFactC31WordBasis

public section

namespace CFSG.KC.WordPts

open CFSG.KLie.CT CFSG.KS CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier CFSG.Quasithin.KGC31
open CFSG.Monster.B.Co2.Native (lettersOK)

variable {n : ℕ}

theorem eq_of_pts {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ} (hH : BaseFaithful H bs)
    {x y : Equiv.Perm (Fin n)} (hx : x ∈ H) (hy : y ∈ H)
    (h : ∀ p : Fin n, (p : ℕ) ∈ bs → x p = y p) : x = y := by
  have h1 := hH (y⁻¹ * x) (H.mul_mem (H.inv_mem hy) hx) fun p hp => by
    rw [Equiv.Perm.mul_apply, h p hp]
    simp
  exact (inv_mul_eq_one.mp h1).symm

theorem bit_eq_true_iff (c r : ℕ) : bit c r = true ↔ c / 2 ^ r % 2 = 1 := by
  have e : Nat.land (Nat.shiftRight c r) 1 = c / 2 ^ r % 2 := by
    change (c >>> r) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold bit
  rw [Nat.beq_eq, e]

@[expose] noncomputable def selGo (c : ℕ) (B : List (List ℤ)) (r : ℕ) : List (List ℤ) :=
  List.rec (motive := fun _ => ℕ → List (List ℤ)) (fun _ => [])
    (fun b _ ih r => Bool.rec (motive := fun _ => List (List ℤ)) (ih (Nat.succ r))
      (b :: ih (Nat.succ r)) (bit c r)) B r

theorem selGo_cons (c : ℕ) (b : List ℤ) (B : List (List ℤ)) (r : ℕ) :
    selGo c (b :: B) r = Bool.rec (motive := fun _ => List (List ℤ)) (selGo c B (r + 1))
      (b :: selGo c B (r + 1)) (bit c r) := rfl

theorem prod_selGo (gs : List (Equiv.Perm (Fin n))) (c : ℕ) :
    ∀ (B : List (List ℤ)) (r : ℕ), ((selGo c B r).map (evalSignedWord gs)).prod =
      eElt (fun i : Fin B.length => evalSignedWord gs B[i]) (bitVec B.length (c / 2 ^ r))
  | [], r => by simp [eElt, selGo]
  | b :: B, r => by
    have ih := prod_selGo gs c B (r + 1)
    have e : c / 2 ^ r / 2 = c / 2 ^ (r + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
    have hval : ((c / 2 ^ r % 2 : ℕ) : ZMod 2).val = c / 2 ^ r % 2 :=
      ZMod.val_cast_of_lt (Nat.mod_lt _ (by norm_num))
    change _ = eElt (n := B.length + 1) (fun i => evalSignedWord gs (b :: B)[i])
      (bitVec (B.length + 1) (c / 2 ^ r))
    rw [eElt_succ, bitVec_succ, bitVec_zero, e, hval]
    have e2 : (fun i : Fin B.length => evalSignedWord gs (b :: B)[(i.succ : Fin (B.length + 1))]) =
        fun i => evalSignedWord gs B[i] := by
      funext i
      rfl
    have e0 : (b :: B)[((0 : Fin (B.length + 1)) : ℕ)] = b := rfl
    rw [e2, ← ih, selGo_cons]
    cases hb : bit c r
    · have h0 : c / 2 ^ r % 2 = 0 := by
        have := (bit_eq_true_iff c r).not.mp (by rw [hb]; decide)
        omega
      rw [h0, pow_zero, one_mul]
    · rw [(bit_eq_true_iff c r).mp hb, pow_one]
      change (List.map (evalSignedWord gs) (b :: _)).prod = _
      rw [List.map_cons, List.prod_cons]
      rfl

theorem prod_selW (gs : List (Equiv.Perm (Fin n))) {B : List (List ℤ)} {k : ℕ} (hk : B.length = k)
    (c : ℕ) : ((selW B c).map (evalSignedWord gs)).prod =
      eElt (fun i : Fin k => evalSignedWord gs (B.getD i [])) (bitVec k c) := by
  subst hk
  have h := prod_selGo gs c B 0
  rw [pow_zero, Nat.div_one] at h
  change (List.map _ (selGo c B 0)).prod = _
  rw [h]
  congr 1
  funext i
  rw [List.getD_eq_getElem _ _ i.2]
  rfl

theorem getD_mem {B : List (List ℤ)} {i : ℕ} (hi : i < B.length) : B.getD i [] ∈ B := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem eElt_mem_of {H : Subgroup (Equiv.Perm (Fin n))} {k : ℕ} {v : Fin k → Equiv.Perm (Fin n)}
    (hv : ∀ i, v i ∈ H) (c : Fin k → ZMod 2) : eElt v c ∈ H :=
  H.list_prod_mem fun x hx => by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact H.pow_mem (hv i) _

theorem allN_ct : ∀ {m : ℕ} {f : ℕ → Bool}, CFSG.KLie.CT.allN m f = true → ∀ i < m, f i = true
  | 0, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | m + 1, f, h, i, hi => by
    change CFSG.KLie.CT.andB (f m) (CFSG.KLie.CT.allN m f) = true at h
    cases hf : f m <;> rw [hf] at h
    · exact absurd h Bool.false_ne_true
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact allN_ct h i hi
      · exact hf

variable {w : ℕ} {G GI : ℕ → ℕ} {gs : List (Equiv.Perm (Fin n))}
  {H : Subgroup (Equiv.Perm (Fin n))} {bs : List ℕ}

theorem fixPtsK_of_prod_eq_one (hG : LetRep n w G GI gs) {xs : List (List ℤ)}
    (hx : ∀ wd ∈ xs, CFSG.Monster.B.Co2.Native.lettersOK gs.length wd = true) (h1 : (xs.map (evalSignedWord gs)).prod = 1) :
    ∀ {bs : List ℕ}, (∀ b ∈ bs, b < n) → fixPtsK n w G GI bs xs = true
  | [], _ => rfl
  | b :: bs, hbs => by
    have hb : b < n := hbs b List.mem_cons_self
    have e : evWs n w G GI xs b = b := by
      have := evWs_eq hG hx ⟨b, hb⟩
      rwa [h1, Equiv.Perm.one_apply] at this
    have ih := fixPtsK_of_prod_eq_one hG hx h1 (fun c hc => hbs c (List.mem_cons_of_mem _ hc))
    change CFSG.KLie.CT.andB (Nat.beq (evWs n w G GI xs b) b) (fixPtsK n w G GI bs xs) = true
    rw [e, Nat.beq_refl, ih]
    rfl

theorem ebasis_of_ebK (hH : BaseFaithful H bs) (hG : LetRep n w G GI gs)
    (hbs : ∀ b ∈ bs, b < n) {B : List (List ℤ)} (hB : ∀ wd ∈ B, CFSG.Monster.B.Co2.Native.lettersOK gs.length wd = true)
    (hBH : ∀ wd ∈ B, evalSignedWord gs wd ∈ H) {k : ℕ} (h : ebK n w G GI bs B k = true) :
    EBasis (fun i : Fin k => evalSignedWord gs (B.getD i [])) := by
  obtain ⟨hlen, hsq, hcomm, hne⟩ := ebK_sound hG hbs hB h
  have hvH : ∀ i : Fin k, evalSignedWord gs (B.getD i []) ∈ H := fun i =>
    hBH _ (getD_mem (by rw [hlen]; exact i.2))
  refine ⟨fun i => ?_, fun i j => ?_, fun c hc => ?_⟩
  · exact eq_of_pts hH (H.mul_mem (hvH i) (hvH i)) H.one_mem fun p hp => hsq i i.2 p hp
  · exact eq_of_pts hH (H.mul_mem (hvH i) (hvH j)) (H.mul_mem (hvH j) (hvH i))
      fun p hp => hcomm i i.2 j j.2 p hp
  · obtain ⟨m, hm, rfl⟩ := exists_bitVec c
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · funext i
      simp [bitVec]
    · exfalso
      obtain ⟨p, hp, hmv⟩ := hne m hpos hm
      rw [prod_selW gs hlen, hc] at hmv
      exact hmv rfl

theorem conj_of_matK (hH : BaseFaithful H bs) (hG : LetRep n w G GI gs) {B : List (List ℤ)}
    (hB : ∀ wd ∈ B, CFSG.Monster.B.Co2.Native.lettersOK gs.length wd = true) (hBH : ∀ wd ∈ B, evalSignedWord gs wd ∈ H)
    {k : ℕ} (hlen : B.length = k) {g : List ℤ} (hg : CFSG.Monster.B.Co2.Native.lettersOK gs.length g = true)
    (hgH : evalSignedWord gs g ∈ H) {M : ℕ} (h : matK n w G GI bs B k g M = true) (i : Fin k) :
    evalSignedWord gs g * evalSignedWord gs (B.getD i []) * (evalSignedWord gs g)⁻¹ =
      eElt (fun j : Fin k => evalSignedWord gs (B.getD j [])) (bitVec k (colF k M i)) := by
  have hvH : ∀ j : Fin k, evalSignedWord gs (B.getD j []) ∈ H := fun j =>
    hBH _ (getD_mem (by rw [hlen]; exact j.2))
  refine eq_of_pts hH (H.mul_mem (H.mul_mem hgH (hvH i)) (H.inv_mem hgH)) (eElt_mem_of hvH _)
    fun p hp => ?_
  rw [matK_sound hG hB hg h i i.2 p hp, prod_selW gs hlen]

@[expose] noncomputable def matOfF (k M : ℕ) : Matrix (Fin k) (Fin k) (ZMod 2) :=
  Matrix.of fun r i => bitVec k (colF k M i) r

theorem mem_eNorm_of_matK (hH : BaseFaithful H bs) (hG : LetRep n w G GI gs)
    {B : List (List ℤ)} (hB : ∀ wd ∈ B, CFSG.Monster.B.Co2.Native.lettersOK gs.length wd = true)
    (hBH : ∀ wd ∈ B, evalSignedWord gs wd ∈ H) {k : ℕ} (hlen : B.length = k)
    (hv : EBasis (fun i : Fin k => evalSignedWord gs (B.getD i []))) {g : List ℤ}
    (hg : CFSG.Monster.B.Co2.Native.lettersOK gs.length g = true) (hgH : evalSignedWord gs g ∈ H) {M : ℕ}
    (h : matK n w G GI bs B k g M = true) : evalSignedWord gs g ∈ eNorm hv :=
  mem_eNorm hv (matOfF k M) fun i => conj_of_matK hH hG hB hBH hlen hg hgH h i

theorem eMat_of_matK (hH : BaseFaithful H bs) (hG : LetRep n w G GI gs)
    {B : List (List ℤ)} (hB : ∀ wd ∈ B, CFSG.Monster.B.Co2.Native.lettersOK gs.length wd = true)
    (hBH : ∀ wd ∈ B, evalSignedWord gs wd ∈ H) {k : ℕ} (hlen : B.length = k)
    (hv : EBasis (fun i : Fin k => evalSignedWord gs (B.getD i []))) {g : List ℤ}
    (hg : CFSG.Monster.B.Co2.Native.lettersOK gs.length g = true) (hgH : evalSignedWord gs g ∈ H) {M : ℕ}
    (h : matK n w G GI bs B k g M = true) :
    eMat hv ⟨_, mem_eNorm_of_matK hH hG hB hBH hlen hv hg hgH h⟩ = matOfF k M :=
  eMat_eq hv _ _ fun i => conj_of_matK hH hG hB hBH hlen hg hgH h i

end CFSG.KC.WordPts

namespace CFSG.KC.OrbPath

theorem card_inf_centralizer_mul_le {Γ : Type*} [Group Γ] [Finite Γ] (K : Subgroup Γ)
    (T : List Γ) {N : ℕ} (c : ℕ → Γ) (hc : ∀ k < N, c k ∈ K)
    (hinj : ∀ k < N, ∀ k' < N,
      (∀ t ∈ T, c k * t * (c k)⁻¹ = c k' * t * (c k')⁻¹) → k = k') :
    Nat.card ↥(K ⊓ Subgroup.centralizer {x | x ∈ T}) * N ≤ Nat.card K := by
  set S := K ⊓ Subgroup.centralizer {x | x ∈ T}
  set S' := S.subgroupOf K
  let f : Fin N → K ⧸ S' := fun k => ((⟨c k, hc k k.2⟩ : K) : K ⧸ S')
  have hf : Function.Injective f := by
    intro a b hab
    have h1 := QuotientGroup.eq.mp hab
    rw [Subgroup.mem_subgroupOf] at h1
    have hcent := (Subgroup.mem_inf.mp h1).2
    rw [Subgroup.mem_centralizer_iff] at hcent
    refine Fin.ext (hinj a a.2 b b.2 fun t ht => ?_)
    have h2 := hcent t ht
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h2
    calc c a * t * (c a)⁻¹ = c a * (t * ((c a)⁻¹ * c b)) * (c b)⁻¹ := by group
      _ = c a * (((c a)⁻¹ * c b) * t) * (c b)⁻¹ := by rw [h2]
      _ = c b * t * (c b)⁻¹ := by group
  have h1 : N ≤ Nat.card (K ⧸ S') := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have h2 : Nat.card S' = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have h3 := Subgroup.card_mul_index S'
  rw [Subgroup.index, h2] at h3
  calc Nat.card S * N ≤ Nat.card S * Nat.card (K ⧸ S') := Nat.mul_le_mul_left _ h1
    _ = Nat.card K := h3

end CFSG.KC.OrbPath

end
