module

public import CFSG.Certificates.Kernel.Misc.O62SoundCert
public import CFSG.Certificates.Kernel.Misc.O62SoundPl

public section

namespace CFSG.KC.Misc.O62

open CFSG.KC.Ord CFSG.KC.Misc
open CFSG.KC.LQT.P (letB impB allN anyN allL anyL)
open CFSG.LargeExtraspecial.O62

theorem impB_true {a b : Bool} (h : impB a b = true) (ha : a = true) : b = true := by
  cases a <;> simp_all [impB]

theorem ev_eq (s : ℕ) : Bool.rec (motive := fun _ => ℕ) 0 1 (Nat.beq s 0) =
    if s = 0 then 1 else 0 := by
  cases h : Nat.beq s 0
  · have : s ≠ 0 := fun h0 => by subst h0; exact absurd h (by decide)
    simp [this]
  · have : s = 0 := Nat.eq_of_beq_eq_true h
    simp [this]

@[expose] noncomputable def wcG (x y : ℕ) : Bool :=
  andB (commK x y) (andB (notB (Nat.beq oneK y)) (notB (Nat.beq (mulK oneK x) y)))

@[expose] noncomputable def wcIn (m : ℕ) (certs : List (ℕ × List ℕ)) (EP : List ℕ)
    (px x Cx : ℕ) : Bool :=
  allN (plCnt Cx) fun j => letB (plAt Cx j) fun y => letB (mulK oneK y) fun y' =>
    letB (mulK (mulK oneK x) y) fun xy =>
      allN (plCnt Cx) fun l => letB (plAt Cx l) fun z =>
        impB (andB (commK y z) (andB (notB (Nat.beq oneK z))
            (andB (notB (Nat.beq (mulK oneK x) z))
              (andB (notB (Nat.beq y' z)) (notB (Nat.beq xy z))))))
          (letB (spanE x y z) fun E => andB (nodup8 E)
            (letB (Bool.rec (motive := fun _ => Nat) 0 1
                (Nat.beq (Nat.add (Nat.add px (plPar Cx j)) (plPar Cx l)) 0))
              fun ev => orB (andB (Nat.beq m 0) (Nat.beq ev 1)) (fitK m ev E certs EP)))

theorem wcX_eq (m IP : ℕ) (certs : List (ℕ × List ℕ)) (EP : List ℕ) (i : ℕ) :
    wcX m IP certs EP i =
      wcIn m certs EP (plPar IP i) (plAt IP i) (plFilter IP (wcG (plAt IP i))) := by
  simp only [wcX, wcIn, letB_eq]
  rfl

theorem wcIn_spec {m : ℕ} {certs : List (ℕ × List ℕ)} {EP : List ℕ} {px x Cx : ℕ}
    (h : wcIn m certs EP px x Cx = true) {j l : ℕ} (hj : j < plCnt Cx) (hl : l < plCnt Cx)
    (hc : Check.comm (plAt Cx j) (plAt Cx l) = true) (h1 : plAt Cx l ≠ Code.one)
    (h2 : plAt Cx l ≠ Code.mul Code.one x) (h3 : plAt Cx l ≠ Code.mul Code.one (plAt Cx j))
    (h4 : plAt Cx l ≠ Code.mul (Code.mul Code.one x) (plAt Cx j)) :
    nodup8 (spanE x (plAt Cx j) (plAt Cx l)) = true ∧
      ((m = 0 ∧ px + plPar Cx j + plPar Cx l = 0) ∨
        fitK m (if px + plPar Cx j + plPar Cx l = 0 then 1 else 0)
          (spanE x (plAt Cx j) (plAt Cx l)) certs EP = true) := by
  unfold wcIn at h
  simp only [letB_eq, allN_iff] at h
  have h' := impB_true (h j hj l hl) (by
    simp only [andB_eq, notB_eq, Bool.and_eq_true, commK_eq, mulK_eq, oneK_eq, beq_eq_decide,
      Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨hc, h1.symm, h2.symm, h3.symm, h4.symm⟩)
  simp only [andB_eq, orB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq, ev_eq,
    Nat.add_eq] at h'
  refine ⟨h'.1, ?_⟩
  rcases h'.2 with ⟨hm, hs⟩ | hf
  · refine Or.inl ⟨hm, ?_⟩
    by_contra hne
    rw [if_neg hne] at hs
    exact absurd hs (by decide)
  · exact Or.inr hf

@[expose] noncomputable def wLane (w : List ℕ) : ℕ := wordC w ||| (w.length % 2) <<< 36

theorem invParK_eq (Tw : List (List ℕ)) :
    invParK Tw = (Tw.filter fun w => Check.isInv (wordC w)).map wLane := by
  induction Tw with
  | nil => rfl
  | cons w t ih =>
    have e : invParK (w :: t) = letLN (wordCK w) fun c => Bool.rec (motive := fun _ => List ℕ)
        (invParK t) (List.cons (Nat.lor c (Nat.shiftLeft (parW w) 36)) (invParK t))
        (isInvK c) := rfl
    rw [e, letLN_eq, wordCK_eq, isInvK_eq, List.filter_cons, ih, parW_eq]
    cases h : Check.isInv (wordC w) <;> simp [wLane]

theorem wLane_lt (w : List ℕ) : wLane w < 2 ^ 37 := by
  have hc := wordC_lt w
  have h : wLane w = (w.length % 2) * 2 ^ 36 + wordC w := by
    unfold wLane
    rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hc, Nat.shiftLeft_eq]
  rw [h]
  have := Nat.mod_lt w.length (show 0 < 2 by norm_num)
  omega

theorem wLane_code (w : List ℕ) : wLane w &&& (2 ^ 36 - 1) = wordC w :=
  (lane_code (wordC_lt w)).1

theorem wLane_par (w : List ℕ) : wLane w >>> 36 = w.length % 2 :=
  (lane_code (wordC_lt w)).2

theorem wcPre_lanes {Tw : List (List ℕ)} {IP : ℕ} (hp : wcPre Tw IP = true) :
    plLanes IP = ((Tw.filter fun w => Check.isInv (wordC w)).map wLane).reverse := by
  unfold wcPre at hp
  simp only [andB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, lenN_eq] at hp
  obtain ⟨hlen, hIP⟩ := hp
  rw [invParK_eq] at hlen hIP
  rw [← hIP]
  refine plLanes_plOf (by simpa using hlen) (fun x hx => ?_)
  obtain ⟨w, _, rfl⟩ := List.mem_map.1 hx
  exact wLane_lt w

theorem exists_index {IP : ℕ} {PS : List (List ℕ)}
    (hlanes : plLanes IP = (PS.map wLane).reverse) {w : List ℕ} (hw : w ∈ PS) :
    ∃ i < plCnt IP, plLane IP i = wLane w := by
  have : wLane w ∈ plLanes IP := by
    rw [hlanes, List.mem_reverse]; exact List.mem_map.2 ⟨w, hw, rfl⟩
  obtain ⟨i, hi, h⟩ := mem_plLanes.1 this
  exact ⟨i, hi, h⟩

theorem wcG_true {x y : ℕ} (hc : Check.comm x y = true) (h1 : y ≠ Code.one)
    (h2 : y ≠ Code.mul Code.one x) : wcG x y = true := by
  simp only [wcG, andB_eq, notB_eq, Bool.and_eq_true, commK_eq, mulK_eq, oneK_eq,
    beq_eq_decide, Bool.not_eq_true', decide_eq_false_iff_not]
  exact ⟨hc, h1.symm, h2.symm⟩

theorem spanC_one (x : ℕ) : Check.spanC [x] = [Code.one, Code.mul Code.one x] := rfl

theorem spanC_two (x y : ℕ) : Check.spanC [y, x] =
    [Code.one, Code.mul Code.one x, Code.mul Code.one y,
      Code.mul (Code.mul Code.one x) y] := rfl

theorem wc_triple {minus : Bool} {PS : List (List ℕ)} {C : List (ℕ × List ℕ)} {EP : List ℕ}
    {IP : ℕ} (hlanes : plLanes IP = (PS.map wLane).reverse) (hc : certK C EP = true)
    (hx : ∀ i < plCnt IP, wcX (if minus then 1 else 0) IP C EP i = true)
    {w₁ w₂ w₃ : List ℕ} (h₁ : w₁ ∈ PS) (h₂ : w₂ ∈ PS) (h₃ : w₃ ∈ PS)
    (hxy : Check.comm (wordC w₁) (wordC w₂) = true) (hy : wordC w₂ ∉ Check.spanC [wordC w₁])
    (hxz : Check.comm (wordC w₁) (wordC w₃) = true)
    (hyz : Check.comm (wordC w₂) (wordC w₃) = true)
    (hz : wordC w₃ ∉ Check.spanC [wordC w₂, wordC w₁]) :
    (Check.spanC [wordC w₃, wordC w₂, wordC w₁]).Nodup ∧
      ((minus = false ∧ (w₁.length % 2 = 0 ∧ w₂.length % 2 = 0 ∧ w₃.length % 2 = 0)) ∨
        ∃ p ∈ C, p.1 = Check.keyOf (Check.spanC [wordC w₃, wordC w₂, wordC w₁]) ∧
          (∀ c ∈ p.2, qB minus c = true) ∧
          ((w₁.length % 2 = 0 ∧ w₂.length % 2 = 0 ∧ w₃.length % 2 = 0) →
            p.2.length % 2 = 0) ∧
          Check.certOK (Check.spanC [wordC w₃, wordC w₂, wordC w₁]) p.2 = true) := by
  obtain ⟨i, hi, hli⟩ := exists_index hlanes h₁
  obtain ⟨i₂, hi₂, hli₂⟩ := exists_index hlanes h₂
  obtain ⟨i₃, hi₃, hli₃⟩ := exists_index hlanes h₃
  have hxa : plAt IP i = wordC w₁ := by rw [plAt_eq, hli, wLane_code]
  have hxp : plPar IP i = w₁.length % 2 := by rw [plPar_eq, hli, wLane_par]
  have hya₂ : plAt IP i₂ = wordC w₂ := by rw [plAt_eq, hli₂, wLane_code]
  have hza₃ : plAt IP i₃ = wordC w₃ := by rw [plAt_eq, hli₃, wLane_code]
  rw [spanC_one] at hy
  rw [spanC_two] at hz
  have hy1 : wordC w₂ ≠ Code.one := fun h => hy (by simp [h])
  have hy2 : wordC w₂ ≠ Code.mul Code.one (wordC w₁) := fun h => hy (by simp [h])
  have hz1 : wordC w₃ ≠ Code.one := fun h => hz (by simp [h])
  have hz2 : wordC w₃ ≠ Code.mul Code.one (wordC w₁) := fun h => hz (by simp [h])
  have hz3 : wordC w₃ ≠ Code.mul Code.one (wordC w₂) := fun h => hz (by simp [h])
  have hz4 : wordC w₃ ≠ Code.mul (Code.mul Code.one (wordC w₁)) (wordC w₂) :=
    fun h => hz (by simp [h])
  obtain ⟨Cx, hCx⟩ : ∃ Cx, Cx = plFilter IP (wcG (plAt IP i)) := ⟨_, rfl⟩
  have hyC : wLane w₂ ∈ plLanes Cx := by
    rw [hCx, mem_plLanes_filter]
    refine ⟨i₂, hi₂, ?_, hli₂⟩
    rw [hxa, hya₂]
    exact wcG_true hxy hy1 hy2
  have hzC : wLane w₃ ∈ plLanes Cx := by
    rw [hCx, mem_plLanes_filter]
    refine ⟨i₃, hi₃, ?_, hli₃⟩
    rw [hxa, hza₃]
    exact wcG_true hxz hz1 hz2
  obtain ⟨j, hj, hlj⟩ := mem_plLanes.1 hyC
  obtain ⟨l, hl, hll⟩ := mem_plLanes.1 hzC
  have hya : plAt Cx j = wordC w₂ := by rw [plAt_eq, hlj, wLane_code]
  have hyp : plPar Cx j = w₂.length % 2 := by rw [plPar_eq, hlj, wLane_par]
  have hza : plAt Cx l = wordC w₃ := by rw [plAt_eq, hll, wLane_code]
  have hzp : plPar Cx l = w₃.length % 2 := by rw [plPar_eq, hll, wLane_par]
  have hxi := hx i hi
  rw [wcX_eq, ← hCx] at hxi
  have hspec := wcIn_spec hxi hj hl (by rw [hya, hza]; exact hyz) (by rw [hza]; exact hz1)
    (by rw [hza, hxa]; exact hz2) (by rw [hza, hya]; exact hz3)
    (by rw [hza, hxa, hya]; exact hz4)
  rw [hxa, hya, hza, hxp, hyp, hzp] at hspec
  have hnd := (nodup8_iff _).1 hspec.1
  rw [e8List_spanE, List.nodup_reverse] at hnd
  refine ⟨hnd, ?_⟩
  rcases hspec.2 with ⟨hm, hs⟩ | hf
  · refine Or.inl ⟨?_, by omega⟩
    cases minus
    · rfl
    · exact absurd hm (by decide)
  · obtain ⟨p, hp, hkey, hq, hpar, hcert⟩ := fit_cert hc hspec.1 hf
    refine Or.inr ⟨p, hp, hkey, ?_, ?_, hcert⟩
    · intro c hc'
      have := hq c hc'
      rwa [qBK_eq] at this
    · rintro ⟨e1, e2, e3⟩
      have h0 := hpar (by rw [if_pos (by omega)])
      rwa [parW_eq] at h0

end CFSG.KC.Misc.O62

end
