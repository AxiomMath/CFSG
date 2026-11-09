module

public import Certificates.Data.Kernel.LocalQT.RankO
public import CFSG.Certificates.Kernel.LocalQTRankQSound

public section

namespace CFSG.KC.LQT.RB

open CFSG.KC.Ord CFSG.KC.LQT.S CFSG.KC.LQT.L CFSG.KC.LQT.PW CFSG.KC.LQT.BC
open CFSG.KC.LQT.PP CFSG.KC.LQT.BW CFSG.KC.LQT.BT CFSG.KC.LQT.RW CFSG.KC.LQT.RF
open CFSG.KC.LQT.BW.Pf CFSG.KC.LQT.BW.Cl CFSG.KC.LQT.RW.Pf CFSG.KC.LQT.RB.Pf
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2 CFSG.QuasithinUnique.Lin2.RankCert
open CFSG.KC.LQT.P (letB impB allL anyL orB_iff andB_iff notB_iff impB_iff beq_iff blt_iff letB_eq)

@[expose] def dfsO (mul : Nat → Nat → Nat) (invs : List Nat) : Nat → Nat → List Nat → List Nat → Bool
  | 0, _, _, _ => true
  | d + 1, h, L, S => invs.any fun c => (decide (h < c) && (!S.contains c &&
      L.all (fun l => mul c l == mul l c))) && dfsO mul invs d c (c :: L) (S ++ S.map (mul c))

theorem dfsWO_eq (mul : Nat → Nat → Nat) (invs : List Nat) :
    ∀ (d h : Nat) (L S : List Nat), dfsWO mul invs d h L S = dfsO mul invs d h L S
  | 0, _, _, _ => rfl
  | d + 1, h, L, S => by
    change anyL invs (fun c => andB (andB (Nat.blt h c) (andB (notB (hasW S c))
      (allL L fun l => Nat.beq (mul c l) (mul l c))))
      (dfsWO mul invs d c (c :: L) (appK S (mapW (mul c) S)))) = _
    rw [anyL_eq, dfsO]
    apply any_congr_mem
    intro c _
    have hb : Nat.blt h c = decide (h < c) := Bool.eq_iff_iff.2 (by rw [P.blt_iff, decide_eq_true_iff])
    rw [andB_eq, andB_eq, andB_eq, hb, notB_eq, hasW_eq, allL_eq, appK_eq, mapW_eq,
      dfsWO_eq mul invs d c]
    congr 3

structure MulLawsO (N : Nat) (mul : Nat → Nat → Nat) : Prop where
  lt : ∀ a < N, ∀ b < N, mul a b < N
  one_mul : ∀ a < N, mul 0 a = a
  mul_one : ∀ a < N, mul a 0 = a
  assoc : ∀ a < N, ∀ b < N, ∀ c < N, mul (mul a b) c = mul a (mul b c)

structure SpanO (N : Nat) (mul : Nat → Nat → Nat) (L S : List Nat) : Prop where
  lt : ∀ s ∈ S, s < N
  nd : S.Nodup
  zero : 0 ∈ S
  closed : ∀ a ∈ S, ∀ b ∈ S, mul a b ∈ S
  inv : ∀ s ∈ S, mul s s = 0
  comm : ∀ a ∈ S, ∀ b ∈ S, mul a b = mul b a
  sub : ∀ l ∈ L, l ∈ S
  prop : ∀ x < N, (∀ l ∈ L, mul x l = mul l x) → ∀ s ∈ S, mul x s = mul s x

section Laws

variable {N : Nat} {mul : Nat → Nat → Nat}

theorem SpanO.nil (H : MulLawsO N mul) (hN : 0 < N) : SpanO N mul [] [0] where
  lt s hs := by rw [List.mem_singleton.1 hs]; exact hN
  nd := List.nodup_singleton 0
  zero := List.mem_singleton_self 0
  closed a ha b hb := by
    rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb, H.one_mul 0 hN]
    exact List.mem_singleton_self 0
  inv s hs := by rw [List.mem_singleton.1 hs, H.one_mul 0 hN]
  comm a ha b hb := by rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]
  sub l hl := absurd hl List.not_mem_nil
  prop x hx _ s hs := by rw [List.mem_singleton.1 hs, H.mul_one x hx, H.one_mul x hx]

theorem SpanO.ext (H : MulLawsO N mul) {L S : List Nat} (hP : SpanO N mul L S) {c : Nat}
    (hc : c < N) (hcS : c ∉ S) (hcc : mul c c = 0) (hcL : ∀ l ∈ L, mul c l = mul l c) :
    SpanO N mul (c :: L) (S ++ S.map (mul c)) := by
  have hcs : ∀ s ∈ S, mul c s = mul s c := hP.prop c hc hcL
  have e1 : ∀ s < N, ∀ t < N, mul (mul c s) t = mul c (mul s t) := fun s hs t ht =>
    H.assoc c hc s hs t ht
  have e2 : ∀ s ∈ S, ∀ t < N, mul s (mul c t) = mul c (mul s t) := fun s hs t ht => by
    rw [← H.assoc s (hP.lt s hs) c hc t ht, ← hcs s hs, e1 s (hP.lt s hs) t ht]
  have e3 : ∀ s ∈ S, ∀ t ∈ S, mul (mul c s) (mul c t) = mul s t := fun s hs t ht => by
    have hs' := hP.lt s hs
    have ht' := hP.lt t ht
    have hst := H.lt s hs' t ht'
    rw [e1 s hs' _ (H.lt c hc t ht'), e2 s hs t ht', ← H.assoc c hc c hc _ hst, hcc,
      H.one_mul _ hst]
  have hcan : ∀ a < N, ∀ b < N, mul c a = mul c b → a = b := fun a ha b hb h => by
    rw [← H.one_mul a ha, ← H.one_mul b hb, ← hcc, H.assoc c hc c hc a ha, H.assoc c hc c hc b hb, h]
  have hmem : ∀ x, x ∈ S ++ S.map (mul c) ↔ x ∈ S ∨ ∃ t ∈ S, mul c t = x := fun x => by
    rw [List.mem_append, List.mem_map]
  have hmemR : ∀ t ∈ S, mul c t ∈ S ++ S.map (mul c) := fun t ht =>
    List.mem_append_right _ (List.mem_map.2 ⟨t, ht, rfl⟩)
  refine ⟨?_, ?_, List.mem_append_left _ hP.zero, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases (hmem x).1 hx with hx | ⟨t, ht, rfl⟩
    · exact hP.lt x hx
    · exact H.lt c hc t (hP.lt t ht)
  · refine List.nodup_append.2 ⟨hP.nd, List.Nodup.map_on (fun a ha b hb h =>
      hcan a (hP.lt a ha) b (hP.lt b hb) h) hP.nd, ?_⟩
    intro a ha b hb hab
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb
    apply hcS
    have ht' := hP.lt t ht
    have e : mul a t = c := by rw [hab, e1 t ht' t ht', hP.inv t ht, H.mul_one c hc]
    rw [← e]
    exact hP.closed a ha t ht
  · intro a ha b hb
    rcases (hmem a).1 ha with ha | ⟨s, hs, rfl⟩ <;> rcases (hmem b).1 hb with hb | ⟨t, ht, rfl⟩
    · exact List.mem_append_left _ (hP.closed a ha b hb)
    · rw [e2 a ha t (hP.lt t ht)]
      exact hmemR _ (hP.closed a ha t ht)
    · rw [e1 s (hP.lt s hs) b (hP.lt b hb)]
      exact hmemR _ (hP.closed s hs b hb)
    · rw [e3 s hs t ht]
      exact List.mem_append_left _ (hP.closed s hs t ht)
  · intro a ha
    rcases (hmem a).1 ha with ha | ⟨s, hs, rfl⟩
    · exact hP.inv a ha
    · rw [e3 s hs s hs, hP.inv s hs]
  · intro a ha b hb
    rcases (hmem a).1 ha with ha | ⟨s, hs, rfl⟩ <;> rcases (hmem b).1 hb with hb | ⟨t, ht, rfl⟩
    · exact hP.comm a ha b hb
    · rw [e2 a ha t (hP.lt t ht), e1 t (hP.lt t ht) a (hP.lt a ha), hP.comm a ha t ht]
    · rw [e2 b hb s (hP.lt s hs), e1 s (hP.lt s hs) b (hP.lt b hb), hP.comm b hb s hs]
    · rw [e3 s hs t ht, e3 t ht s hs, hP.comm s hs t ht]
  · intro l hl
    rcases List.mem_cons.1 hl with rfl | hl
    · have h := hmemR 0 hP.zero
      rwa [H.mul_one l hc] at h
    · exact List.mem_append_left _ (hP.sub l hl)
  · intro x hx hxL a ha
    have hxc := hxL c (List.mem_cons_self ..)
    have hxS := hP.prop x hx fun l hl => hxL l (List.mem_cons_of_mem _ hl)
    rcases (hmem a).1 ha with ha | ⟨s, hs, rfl⟩
    · exact hxS a ha
    · have hs' := hP.lt s hs
      rw [← H.assoc x hx c hc s hs', hxc, H.assoc c hc x hx s hs', hxS s hs, e1 s hs' x hx]

theorem SpanO.of_dfs (H : MulLawsO N mul) {invs : List Nat}
    (hinv : ∀ c ∈ invs, c < N ∧ mul c c = 0) :
    ∀ (d : Nat) (L S : List Nat), SpanO N mul L S → dfs mul invs d L S = true →
      ∃ L' E, SpanO N mul L' E ∧ (∀ s ∈ S, s ∈ E) ∧ S.length * 2 ^ d ≤ E.length
  | 0, L, S, hP, _ => ⟨L, S, hP, fun _ h => h, by simp⟩
  | d + 1, L, S, hP, h => by
    rw [dfs, List.any_eq_true] at h
    obtain ⟨c, hc, h⟩ := h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have hcS : c ∉ S := fun hm => by simp [hm] at h1
    have hcL : ∀ l ∈ L, mul c l = mul l c := fun l hl => beq_iff_eq.1 (List.all_eq_true.1 h2 l hl)
    obtain ⟨hcN, hcc⟩ := hinv c hc
    obtain ⟨L', E, hE, hSE, hlen⟩ := SpanO.of_dfs H hinv d _ _ (hP.ext H hcN hcS hcc hcL) h3
    refine ⟨L', E, hE, fun s hs => hSE s (List.mem_append_left _ hs), ?_⟩
    rw [List.length_append, List.length_map] at hlen
    rw [pow_succ]
    generalize 2 ^ d = p at hlen ⊢
    have e : S.length * (p * 2) = (S.length + S.length) * p := by ring
    rw [e]
    exact hlen

theorem SpanO.dfsO_of (H : MulLawsO N mul) {invs : List Nat}
    (hinvs : ∀ c < N, c ≠ 0 → mul c c = 0 → c ∈ invs) {L' E : List Nat} (hE : SpanO N mul L' E) :
    ∀ (d h : Nat) (L S : List Nat), SpanO N mul L S → (∀ s ∈ S, s ∈ E) →
      (∀ x ∈ E, x ≤ h → x ∈ S) → S.length * 2 ^ d ≤ E.length → dfsO mul invs d h L S = true
  | 0, _, _, _, _, _, _, _ => rfl
  | d + 1, h, L, S, hP, hSE, hI, hlen => by
    classical
    have hex : ∃ m, m ∈ E ∧ m ∉ S := by
      by_contra hno
      push Not at hno
      have hsub := (hE.nd.subperm hno).length_le
      have h0 : 0 < S.length := List.length_pos_of_mem hP.zero
      have h2 : 2 ≤ 2 ^ (d + 1) := by
        rw [pow_succ]
        have := Nat.one_le_two_pow (n := d)
        omega
      generalize 2 ^ (d + 1) = p at hlen h2
      have : S.length * 2 ≤ S.length * p := Nat.mul_le_mul_left _ h2
      omega
    have hcE := (Nat.find_spec hex).1
    have hcS := (Nat.find_spec hex).2
    have hmin : ∀ x ∈ E, x < Nat.find hex → x ∈ S := fun x hx hxc => by
      by_contra hxs
      exact Nat.find_min hex hxc ⟨hx, hxs⟩
    generalize Nat.find hex = c at hcE hcS hmin
    have hcN := hE.lt c hcE
    have hhc : h < c := by
      by_contra hle
      push Not at hle
      exact hcS (hI c hcE hle)
    have hc0 : c ≠ 0 := fun h0 => hcS (h0 ▸ hP.zero)
    have hcc := hE.inv c hcE
    have hcL : ∀ l ∈ L, mul c l = mul l c := fun l hl => hE.comm c hcE l (hSE l (hP.sub l hl))
    rw [dfsO, List.any_eq_true]
    refine ⟨c, hinvs c hcN hc0 hcc, ?_⟩
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff]
    refine ⟨⟨hhc, by simpa using hcS, List.all_eq_true.2 fun l hl => beq_iff_eq.2 (hcL l hl)⟩, ?_⟩
    apply SpanO.dfsO_of H hinvs hE d c (c :: L) _ (hP.ext H hcN hcS hcc hcL)
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hSE x hx
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
        exact hE.closed c hcE t (hSE t ht)
    · intro x hx hxc
      rcases Nat.lt_or_eq_of_le hxc with hlt | rfl
      · exact List.mem_append_left _ (hmin x hx hlt)
      · exact List.mem_append_right S (List.mem_map.2 ⟨0, hP.zero, H.mul_one x hcN⟩)
    · rw [List.length_append, List.length_map]
      rw [pow_succ] at hlen
      generalize 2 ^ d = p at hlen ⊢
      have e : S.length * (p * 2) = (S.length + S.length) * p := by ring
      rw [← e]
      exact hlen

theorem branchF_of_branchFO (H : MulLawsO N mul) {z d : Nat} (hz : z < N) (hz0 : z ≠ 0)
    (hzz : mul z z = 0) {invs : List Nat} (hinvs : ∀ c, c ∈ invs ↔ c < N ∧ c ≠ 0 ∧ mul c c = 0)
    (hO : ∀ c ∈ invs, branchFO mul invs z d c = true) :
    ∀ c ∈ invs, branchF mul invs z d c = true := by
  classical
  intro c hc
  obtain ⟨hcN, -, hcc⟩ := (hinvs c).1 hc
  have P1 : SpanO N mul [z] [0, z] := by
    have h := (SpanO.nil H (by omega)).ext H hz (by simpa using hz0) hzz (fun _ h => absurd h List.not_mem_nil)
    have e : [0] ++ [0].map (mul z) = [0, z] := by simp [H.mul_one z hz]
    rwa [e] at h
  by_contra hb
  have hb' : branchF mul invs z d c = false := Bool.eq_false_iff.2 hb
  unfold branchF at hb'
  rw [notB_eq, Bool.not_eq_false', andB_eq, andB_eq, Bool.and_eq_true, Bool.and_eq_true, notB_eq,
    hasW_eq, appK_eq, mapW_eq, dfsW_eq] at hb'
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb'
  have hcS : c ∉ [0, z] := fun hm => by simp [hm] at h1
  have hcz := P.beq_iff.1 h2
  have P2 := P1.ext H hcN hcS hcc (fun l hl => by rw [List.mem_singleton.1 hl]; exact hcz)
  obtain ⟨L', E, hE, hSE, hlen⟩ := SpanO.of_dfs H
    (fun c hc => ⟨((hinvs c).1 hc).1, ((hinvs c).1 hc).2.2⟩) d _ _ P2 h3
  have hzE : z ∈ E := hSE z (by simp)
  have hex : ∃ m, m ∈ E ∧ m ∉ [0, z] := by
    by_contra hno
    push Not at hno
    have hsub := (hE.nd.subperm hno).length_le
    have h2d := Nat.one_le_two_pow (n := d)
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil] at hlen hsub
    generalize 2 ^ d = p at hlen h2d
    omega
  have hcE := (Nat.find_spec hex).1
  have hcS' := (Nat.find_spec hex).2
  have hmin : ∀ x ∈ E, x < Nat.find hex → x ∈ [0, z] := fun x hx hxc => by
    by_contra hxs
    exact Nat.find_min hex hxc ⟨hx, hxs⟩
  generalize Nat.find hex = c' at hcE hcS' hmin
  have hc'N := hE.lt c' hcE
  have hc'0 : c' ≠ 0 := fun h0 => hcS' (by simp [h0])
  have hc'c := hE.inv c' hcE
  have hc'z := hE.comm c' hcE z hzE
  have P2' := P1.ext H hc'N hcS' hc'c (fun l hl => by rw [List.mem_singleton.1 hl]; exact hc'z)
  have hd := SpanO.dfsO_of H (fun x hx h0 hxx => (hinvs x).2 ⟨hx, h0, hxx⟩) hE d c' [c', z] _ P2'
    (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hSE x (List.mem_append_left _ hx)
      · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
        exact hE.closed c' hcE t (hSE t (List.mem_append_left _ ht)))
    (by
      intro x hx hxc
      rcases Nat.lt_or_eq_of_le hxc with hlt | rfl
      · exact List.mem_append_left _ (hmin x hx hlt)
      · exact List.mem_append_right _ (List.mem_map.2 ⟨0, by simp, H.mul_one x hc'N⟩))
    (by simpa using hlen)
  have hb2 := hO c' ((hinvs c').2 ⟨hc'N, hc'0, hc'c⟩)
  unfold branchFO at hb2
  rw [appK_eq, mapW_eq, dfsWO_eq, hd, notB_eq, andB_eq, andB_eq, notB_eq, hasW_eq] at hb2
  have e1 : ([0, z].contains c') = false := by simpa using hcS'
  have e2 : Nat.beq (mul c' z) (mul z c') = true := P.beq_iff.2 hc'z
  rw [e1, e2] at hb2
  exact absurd hb2 (by decide)

end Laws

theorem mulLawsO_of_rowRU {W g N : Nat} {PT CT QT UP UI : Nat → Nat} (hg : 0 < g) (hN : 0 < N)
    (hq : ∀ i < N, rowRQ W g N PT CT QT i = true)
    (he : ∀ x < N, eqvRU W g N CT QT UP UI x = true) :
    MulLawsO N (mulRQ W QT) := by
  have hm := mulRQ_of_rowRQ hq N
  have hlt : ∀ a < N, ∀ b < N, mulRQ W QT a b < N := fun a ha b hb => (hm a ha ha b hb).2
  have h1 : ∀ a < N, mulRQ W QT 0 a = a := (rowRQ_spec hq hN).2.1 rfl
  have hpar : ∀ a < N, a ≠ 0 → fieldT W PT a < a ∧ ∀ k < N, mulRQ W QT a k =
      fieldT W CT (Nat.add (Nat.mul (mulRQ W QT (fieldT W PT a) k) (Nat.add g g))
        (genIdxT W g (Nat.add g g) PT CT a)) := fun a ha ha0 => rowRQ_step hq ha ha0
  have hgi : ∀ a, genIdxT W g (Nat.add g g) PT CT a < g := by
    intro a
    rw [genIdxT, findW_eq (fun _ _ => rfl)]
    exact find_getD_lt hg _
  have hand : ∀ a b : Bool, andB a b = true → a = true ∧ b = true := fun a b h => by
    rw [andB_eq, Bool.and_eq_true] at h
    exact h
  have hE : ∀ x < N, mulRQ W QT x 0 = x ∧
      (x ≠ 0 → fieldT W UP x < x ∧ fieldT W UI x < g ∧
        mulRQ W QT (fieldT W UP x) (fieldT W CT (fieldT W UI x)) = x) ∧
      ∀ j < g, fieldT W CT (Nat.add (Nat.mul x (Nat.add g g)) j) < N ∧ ∀ i < g,
        mulRQ W QT (fieldT W CT (Nat.add (Nat.mul x (Nat.add g g)) j)) (fieldT W CT i) =
          fieldT W CT (Nat.add (Nat.mul (mulRQ W QT x (fieldT W CT i)) (Nat.add g g)) j) := by
    intro x hx
    have h := he x hx
    rw [eqvRU, letRQ_eq] at h
    obtain ⟨h0, h⟩ := hand _ _ h
    obtain ⟨ht, hs⟩ := hand _ _ h
    refine ⟨P.beq_iff.1 h0, fun hx0 => ?_, fun j hj => ?_⟩
    · have hb : Nat.beq x 0 = false := by
        cases h : Nat.beq x 0
        · rfl
        · exact absurd (P.beq_iff.1 h) hx0
      rw [hb] at ht
      obtain ⟨ht1, ht⟩ := hand _ _ ht
      obtain ⟨ht2, ht3⟩ := hand _ _ ht
      exact ⟨P.blt_iff.1 ht1, P.blt_iff.1 ht2, P.beq_iff.1 ht3⟩
    · have h2 := allR_true hs j hj
      simp only [Nat.zero_add] at h2
      rw [letRQ_eq] at h2
      obtain ⟨h2a, h2b⟩ := hand _ _ h2
      refine ⟨P.blt_iff.1 h2a, fun i hi => ?_⟩
      have h3 := allR_true h2b i hi
      simp only [Nat.zero_add] at h3
      exact P.beq_iff.1 h3
  have heN : ∀ i < g, fieldT W CT i < N := by
    intro i hi
    have h := ((hE 0 hN).2.2 i hi).1
    have e : Nat.add (Nat.mul 0 (Nat.add g g)) i = i := by simp
    rwa [e] at h
  have hR : ∀ a < N, ∀ k < N, ∀ i < g, mulRQ W QT a (mulRQ W QT k (fieldT W CT i)) =
      mulRQ W QT (mulRQ W QT a k) (fieldT W CT i) := by
    intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha k hk i hi
      have hki := hlt k hk _ (heN i hi)
      rcases Nat.eq_zero_or_pos a with rfl | ha0
      · rw [h1 _ hki, h1 k hk]
      · obtain ⟨hpa, hpk⟩ := hpar a ha (by omega)
        have hpN : fieldT W PT a < N := by omega
        rw [hpk _ hki, ih _ hpa hpN k hk i hi, hpk k hk,
          ((hE _ (hlt _ hpN k hk)).2.2 _ (hgi a)).2 i hi]
  have huniq : ∀ A B : Nat → Nat,
      (∀ k < N, ∀ i < g, A (mulRQ W QT k (fieldT W CT i)) = mulRQ W QT (A k) (fieldT W CT i)) →
      (∀ k < N, ∀ i < g, B (mulRQ W QT k (fieldT W CT i)) = mulRQ W QT (B k) (fieldT W CT i)) →
      A 0 = B 0 → ∀ k < N, A k = B k := by
    intro A B hA hB h0 k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact h0
      · obtain ⟨hp, hi, hpe⟩ := (hE k hk).2.1 (by omega)
        rw [← hpe, hA _ (by omega) _ hi, hB _ (by omega) _ hi, ih _ hp (by omega)]
  have hstep : ∀ x < N, ∀ j < g,
      fieldT W CT (Nat.add (Nat.mul x (Nat.add g g)) j) < N ∧ ∀ k < N,
        mulRQ W QT (fieldT W CT (Nat.add (Nat.mul x (Nat.add g g)) j)) k =
          fieldT W CT (Nat.add (Nat.mul (mulRQ W QT x k) (Nat.add g g)) j) := by
    intro x hx j hj
    have hyN := ((hE x hx).2.2 j hj).1
    refine ⟨hyN, huniq (mulRQ W QT (fieldT W CT (Nat.add (Nat.mul x (Nat.add g g)) j)))
      (fun k => fieldT W CT (Nat.add (Nat.mul (mulRQ W QT x k) (Nat.add g g)) j))
      (fun k hk i hi => hR _ hyN k hk i hi) (fun k hk i hi => ?_) ?_⟩
    · rw [hR x hx k hk i hi, ((hE _ (hlt x hx k hk)).2.2 j hj).2 i hi]
    · rw [(hE _ hyN).1, (hE x hx).1]
  refine ⟨hlt, h1, fun a ha => (hE a ha).1, ?_⟩
  · intro a
    induction a using Nat.strong_induction_on with
    | _ a ih =>
      intro ha b hb c hc
      rcases Nat.eq_zero_or_pos a with rfl | ha0
      · rw [h1 b hb, h1 _ (hlt b hb c hc)]
      · obtain ⟨hpa, hk⟩ := hpar a ha (by omega)
        have hpN : fieldT W PT a < N := by omega
        rw [hk b hb, (hstep _ (hlt _ hpN b hb) _ (hgi a)).2 c hc, ih _ hpa hpN b hb c hc,
          ← hk _ (hlt b hb c hc)]

theorem mem_invsB_iff {N : Nat} {mul : Nat → Nat → Nat} (c : Nat) :
    c ∈ invsB N mul ↔ c < N ∧ c ≠ 0 ∧ mul c c = 0 := by
  unfold invsB
  rw [filterN_eq, List.mem_filter, List.mem_range, andB_eq, notB_eq, nbeq_eq, nbeq_eq]
  simp

theorem rankBQ_of_rankBO {W g N : Nat} {PT CT QT UP UI : Nat → Nat} (hg : 0 < g)
    (hq : ∀ i < N, rowRQ W g N PT CT QT i = true)
    (he : ∀ x < N, eqvRU W g N CT QT UP UI x = true)
    {d zi K L : Nat} (hz : zi < N) (hz0 : zi ≠ 0) (hzz : mulRQ W QT zi zi = 0)
    (hcov : (invsB N (mulRQ W QT)).length ≤ K * L)
    (h : ∀ j < K, rankBO W N QT d zi (j * L) L = true) :
    ∀ j < K, rankBQ W N QT d zi (j * L) L = true := by
  have H := mulLawsO_of_rowRU hg (by omega) hq he
  have hO : ∀ c ∈ invsB N (mulRQ W QT), branchFO (mulRQ W QT) (invsB N (mulRQ W QT)) zi d c = true := by
    intro c hc
    obtain ⟨j, hj, hjs⟩ := mem_slice hcov hc
    have hb := h j hj
    change allL _ _ = true at hb
    rw [allL_eq, List.all_eq_true] at hb
    exact hb c hjs
  have hF := branchF_of_branchFO H hz hz0 hzz mem_invsB_iff hO
  intro j _
  change allL _ _ = true
  rw [allL_eq, List.all_eq_true]
  intro c hc
  exact hF c (List.mem_of_mem_drop (List.mem_of_mem_take (by rw [sliceK] at hc; exact hc)))

end CFSG.KC.LQT.RB

end
