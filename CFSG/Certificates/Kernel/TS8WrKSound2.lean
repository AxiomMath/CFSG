module

public import CFSG.Certificates.Kernel.TS8WrKSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrSylow

public section

namespace CFSG.KC.TS8WrK

open CFSG.EvenSporadicStandard.Fin76b.TS8Wr CFSG.QuasithinUnique.A6Facts

theorem orB_eq_true {a b : Bool} : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem notB_eq_true {a : Bool} : notB a = true ↔ a = false := by
  cases a <;> decide

theorem beq_eq_true {x y : Nat} : Nat.beq x y = true ↔ x = y :=
  ⟨Nat.eq_of_beq_eq_true, fun h => by rw [h]; exact Nat.beq_refl y⟩

theorem beq_false {x y : Nat} (h : x ≠ y) : Nat.beq x y = false := by
  cases hb : Nat.beq x y
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem blt_eq_true {x y : Nat} : Nat.blt x y = true ↔ x < y :=
  ⟨Nat.le_of_ble_eq_true, Nat.ble_eq_true_of_le⟩

theorem allL_eq_true {l : List Nat} {f : Nat → Bool} :
    allL l f = true ↔ ∀ x ∈ l, f x = true := by
  induction l with
  | nil => exact ⟨fun _ x hx => by simp at hx, fun _ => rfl⟩
  | cons y l ih =>
    change andB (f y) (allL l f) = true ↔ _
    rw [andB_eq_true, ih, List.forall_mem_cons]

theorem memN_eq_true {x : Nat} {l : List Nat} : memN x l = true ↔ x ∈ l := by
  induction l with
  | nil => exact ⟨fun h => Bool.noConfusion h, fun h => by simp at h⟩
  | cons y l ih =>
    change orB (Nat.beq x y) (memN x l) = true ↔ _
    rw [orB_eq_true, ih, List.mem_cons, beq_eq_true]

theorem filterL_eq (l : List Nat) (f : Nat → Bool) : filterL l f = l.filter f := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    rw [List.filter_cons]
    change Bool.rec (motive := fun _ => List Nat) (filterL l f) (y :: filterL l f) (f y) = _
    cases f y
    · exact ih
    · exact congrArg (List.cons y) ih

theorem appL_eq (l m : List Nat) : appL l m = l ++ m := by
  induction l with
  | nil => rfl
  | cons y l ih => exact congrArg (List.cons y) ih

theorem lenP_eq (l : List (Nat × Nat)) : lenP l = l.length := by
  induction l with
  | nil => rfl
  | cons y l ih => exact congrArg Nat.succ ih

theorem memKey_sound {x : Nat} {ZA : List (Nat × List Nat)} (h : memKey x ZA = true) :
    ∃ al, (x, al) ∈ ZA := by
  induction ZA with
  | nil => exact Bool.noConfusion h
  | cons p ZA ih =>
    have h' : orB (Nat.beq x p.1) (memKey x ZA) = true := h
    rcases orB_eq_true.1 h' with h1 | h1
    · refine ⟨p.2, ?_⟩
      rw [beq_eq_true.1 h1]
      exact List.mem_cons_self
    · obtain ⟨al, hal⟩ := ih h1
      exact ⟨al, List.mem_cons_of_mem _ hal⟩

theorem flatZA_cons (p : Nat × List Nat) (ZA : List (Nat × List Nat)) :
    flatZA (p :: ZA) = p.2.map (fun a => (p.1, a)) ++ flatZA ZA := by
  obtain ⟨z, l⟩ := p
  change List.rec (motive := fun _ => List (Nat × Nat)) (flatZA ZA)
    (fun a _ ih' => (z, a) :: ih') l = _
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (List.cons (z, a)) ih

theorem mem_flatZA {ZA : List (Nat × List Nat)} {z a : Nat} {al : List Nat} (h : (z, al) ∈ ZA)
    (ha : a ∈ al) : (z, a) ∈ flatZA ZA := by
  induction ZA with
  | nil => simp at h
  | cons p ZA ih =>
    rw [flatZA_cons, List.mem_append]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (List.mem_map.2 ⟨a, ha, rfl⟩)
    · exact Or.inr (ih h)

theorem exists_nthP {l : List (Nat × Nat)} {p : Nat × Nat} (h : p ∈ l) :
    ∃ k < l.length, nthP l k = p := by
  induction l with
  | nil => simp at h
  | cons q l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, Nat.succ_pos _, rfl⟩
    · obtain ⟨k, hk, hkp⟩ := ih h
      exact ⟨k + 1, Nat.succ_lt_succ hk, hkp⟩

theorem lenL_eq (l : List Nat) : lenL l = l.length := by
  induction l with
  | nil => rfl
  | cons y l ih => exact congrArg Nat.succ ih

theorem sumLen_eq (RT : List (Nat × List Nat)) : sumLen RT = (RT.flatMap Prod.snd).length := by
  induction RT with
  | nil => rfl
  | cons p RT ih =>
    change lenL p.2 + sumLen RT = _
    rw [List.flatMap_cons, List.length_append, ih, lenL_eq]

theorem rootsGo_sound {TB s : Nat} : ∀ {l : List Nat} {lo : Nat}, rootsGo TB s l lo = true →
    l.Pairwise (· < ·) ∧ ∀ r ∈ l, lo ≤ r ∧ r < 2048 ∧ mulK TB r r = s
  | [], _, _ => ⟨List.Pairwise.nil, fun r hr => by simp at hr⟩
  | r :: l, lo, h => by
    have h' : andB (Nat.ble lo r) (andB (Nat.blt r 2048) (andB (Nat.beq (mulK TB r r) s)
        (rootsGo TB s l (Nat.succ r)))) = true := h
    simp only [andB_eq_true, blt_eq_true, beq_eq_true] at h'
    obtain ⟨h1, h2, h3, h4⟩ := h'
    have h1' := Nat.le_of_ble_eq_true h1
    obtain ⟨ih1, ih2⟩ := rootsGo_sound h4
    refine ⟨List.Pairwise.cons (fun r' hr' => (ih2 r' hr').1) ih1, ?_⟩
    intro r' hr'
    rcases List.mem_cons.1 hr' with rfl | hr'
    · exact ⟨h1', h2, h3⟩
    · obtain ⟨q1, q2⟩ := ih2 r' hr'
      exact ⟨by omega, q2⟩

theorem rtGo_sound {TB : Nat} : ∀ {RT : List (Nat × List Nat)} {lo : Nat}, rtGo TB RT lo = true →
    RT.Pairwise (fun p q => p.1 < q.1) ∧ ∀ p ∈ RT, lo ≤ p.1 ∧ p.2.Pairwise (· < ·) ∧
      ∀ r ∈ p.2, r < 2048 ∧ mulK TB r r = p.1
  | [], _, _ => ⟨List.Pairwise.nil, fun p hp => by simp at hp⟩
  | p :: RT, lo, h => by
    have h' : andB (Nat.ble lo p.1) (andB (rootsGo TB p.1 p.2 0)
        (rtGo TB RT (Nat.succ p.1))) = true := h
    rw [andB_eq_true, andB_eq_true] at h'
    obtain ⟨h1, h2, h3⟩ := h'
    have h1' := Nat.le_of_ble_eq_true h1
    obtain ⟨ih1, ih2⟩ := rtGo_sound h3
    obtain ⟨r1, r2⟩ := rootsGo_sound h2
    refine ⟨List.Pairwise.cons (fun q hq => (ih2 q hq).1) ih1, ?_⟩
    intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact ⟨h1', r1, fun r hr => (r2 r hr).2⟩
    · obtain ⟨q1, q2⟩ := ih2 q hq
      exact ⟨by omega, q2⟩

theorem rootsOf_of_mem : ∀ {RT : List (Nat × List Nat)}, RT.Pairwise (fun p q => p.1 < q.1) →
    ∀ {p : Nat × List Nat}, p ∈ RT → rootsOf RT p.1 = p.2
  | [], _, _, hp => by simp at hp
  | q :: RT, hpw, p, hp => by
    change Bool.rec (motive := fun _ => List Nat) (rootsOf RT p.1) q.2 (Nat.beq q.1 p.1) = p.2
    rw [List.pairwise_cons] at hpw
    rcases List.mem_cons.1 hp with rfl | hp
    · rw [Nat.beq_refl]
    · rw [beq_false (Nat.ne_of_lt (hpw.1 p hp))]
      exact rootsOf_of_mem hpw.2 hp

theorem rtOK_sound {TB : Nat} {RT : List (Nat × List Nat)} (h : rtOK TB RT = true) :
    ∀ c < 2048, c ∈ rootsOf RT (mulK TB c c) := by
  intro c hc
  have h' := andB_eq_true.1 h
  obtain ⟨hpw, hall⟩ := rtGo_sound h'.2
  have hlen : (RT.flatMap Prod.snd).length = 2048 := by
    rw [← sumLen_eq]
    exact beq_eq_true.1 h'.1
  have hnd : (RT.flatMap Prod.snd).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun p hp => (hall p hp).2.1.imp Nat.ne_of_lt, ?_⟩
    refine hpw.imp_of_mem fun {p q} hp hq hlt => ?_
    change List.Disjoint p.2 q.2
    intro r hr1 hr2
    have e1 := ((hall p hp).2.2 r hr1).2
    have e2 := ((hall q hq).2.2 r hr2).2
    omega
  have hsub : (RT.flatMap Prod.snd).toFinset = Finset.range 2048 := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [List.mem_toFinset, List.mem_flatMap] at hx
      obtain ⟨p, hp, hx⟩ := hx
      exact Finset.mem_range.2 ((hall p hp).2.2 x hx).1
    · rw [Finset.card_range, List.toFinset_card_of_nodup hnd, hlen]
  have hcF : c ∈ RT.flatMap Prod.snd := by
    rw [← List.mem_toFinset, hsub]
    exact Finset.mem_range.2 hc
  obtain ⟨p, hp, hcp⟩ := List.mem_flatMap.1 hcF
  rw [((hall p hp).2.2 c hcp).2, rootsOf_of_mem hpw hp]
  exact hcp

theorem zGo_sound {TB one : Nat} {ZA : List (Nat × List Nat)} :
    ∀ {xs : List Nat} {zc : List (Nat × Nat)}, zGo TB one ZA xs zc = true →
      ∀ x ∈ xs, ∃ p, zRec TB one ZA x p = true
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], h, _, _ => Bool.noConfusion (h : false = true)
  | y :: xs, p :: zc, h, x, hx => by
    have h' : andB (zRec TB one ZA y p) (zGo TB one ZA xs zc) = true := h
    rw [andB_eq_true] at h'
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨p, h'.1⟩
    · exact zGo_sound h'.2 x hx

theorem aGo_sound {TB z : Nat} {al : List Nat} :
    ∀ {xs : List Nat} {ac : List (Nat × Nat)}, aGo TB z al xs ac = true →
      ∀ x ∈ xs, ∃ p, aRec TB z al x p = true
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], h, _, _ => Bool.noConfusion (h : false = true)
  | y :: xs, p :: ac, h, x, hx => by
    have h' : andB (aRec TB z al y p) (aGo TB z al xs ac) = true := h
    rw [andB_eq_true] at h'
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨p, h'.1⟩
    · exact aGo_sound h'.2 x hx

theorem zaGo_sound {TB : Nat} {RT : List (Nat × List Nat)} {one : Nat} :
    ∀ {ZA : List (Nat × List Nat)} {AC : List (List (Nat × Nat))}, zaGo TB RT one ZA AC = true →
      ∀ p ∈ ZA, p.1 < 2048 ∧ (∀ r ∈ p.2, r < 2048) ∧
        ∀ x ∈ filterL (rootsOf RT one) (aCand TB one p.1), ∃ q, aRec TB p.1 p.2 x q = true
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], h, _, _ => Bool.noConfusion (h : false = true)
  | q :: ZA, acl :: AC, h, p, hp => by
    have h' : andB (Nat.blt q.1 2048) (andB (allL q.2 fun r => Nat.blt r 2048)
        (andB (aGo TB q.1 q.2 (filterL (rootsOf RT one) (aCand TB one q.1)) acl)
          (zaGo TB RT one ZA AC))) = true := h
    simp only [andB_eq_true, allL_eq_true, blt_eq_true] at h'
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨h'.1, h'.2.1, aGo_sound h'.2.2.1⟩
    · exact zaGo_sound h'.2.2.2 p hp

theorem zaGo_of_zaOK {TB : Nat} {RT : List (Nat × List Nat)} {one : Nat}
    {ZA : List (Nat × List Nat)} {AC : List (List (Nat × Nat))} {n : Nat}
    (hA : zaOK TB RT one ZA AC n = true) : zaGo TB RT one ZA AC = true :=
  (andB_eq_true.1 hA).2

theorem rowOK_of_checks {TB : Nat} {RT : List (Nat × List Nat)} {one : Nat}
    {ZA : List (Nat × List Nat)} {AC : List (List (Nat × Nat))} {n : Nat}
    (hA : zaOK TB RT one ZA AC n = true)
    (hrows : ∀ k, 0 ≤ k → k < n → ∃ z a, rowChk TB RT one ZA k z a = true)
    {z a : Nat} {al : List Nat} (hzal : (z, al) ∈ ZA) (ha : a ∈ al) : rowOK TB RT one z a = true := by
  have hA' := hA
  unfold zaOK at hA'
  rw [andB_eq_true, beq_eq_true, lenP_eq] at hA'
  obtain ⟨k, hk, hkp⟩ := exists_nthP (mem_flatZA hzal ha)
  obtain ⟨z', a', hc⟩ := hrows k (Nat.zero_le k) (hA'.1 ▸ hk)
  unfold rowChk at hc
  rw [andB_eq_true, andB_eq_true, beq_eq_true, beq_eq_true, hkp] at hc
  obtain ⟨⟨rfl, rfl⟩, hc⟩ := hc
  exact hc

section E

variable {G : Type*} [Group G]

def InE (α t e : G) : Prop := e = 1 ∨ e = α ∨ e = t ∨ e = α * t

theorem inE_mul {α t e : G} (hαα : α * α = 1) (htt : t * t = 1) (hc : α * t = t * α)
    (he : InE α t e) : InE α t (e * α) ∧ InE α t (e * t) ∧ InE α t (e * (α * t)) := by
  unfold InE
  rcases he with rfl | rfl | rfl | rfl
  · simp
  · refine ⟨Or.inl hαα, Or.inr (Or.inr (Or.inr rfl)), Or.inr (Or.inr (Or.inl ?_))⟩
    rw [← mul_assoc, hαα, one_mul]
  · refine ⟨Or.inr (Or.inr (Or.inr hc.symm)), Or.inl htt, Or.inr (Or.inl ?_)⟩
    rw [← mul_assoc, ← hc, mul_assoc, htt, mul_one]
  · refine ⟨Or.inr (Or.inr (Or.inl ?_)), Or.inr (Or.inl ?_), Or.inl ?_⟩
    · rw [mul_assoc, ← hc, ← mul_assoc, hαα, one_mul]
    · rw [mul_assoc, htt, mul_one]
    · rw [mul_assoc, ← mul_assoc t, ← hc, mul_assoc α, htt, mul_one, hαα]

theorem inE_sq {α t e : G} (hαα : α * α = 1) (htt : t * t = 1) (hc : α * t = t * α)
    (he : InE α t e) : e * e = 1 := by
  rcases he with rfl | rfl | rfl | rfl
  · exact mul_one 1
  · exact hαα
  · exact htt
  · rw [mul_assoc, ← mul_assoc t, ← hc, mul_assoc α, htt, mul_one, hαα]

theorem comm_E {α t e x : G} (hxα : x * α = α * x) (hxt : x * t = t * x) (he : InE α t e) :
    x * e = e * x := by
  rcases he with rfl | rfl | rfl | rfl
  · rw [mul_one, one_mul]
  · exact hxα
  · exact hxt
  · rw [← mul_assoc, hxα, mul_assoc, hxt, ← mul_assoc]

theorem inE_cent {α t e : G} (hc : α * t = t * α) (he : InE α t e) :
    e * α = α * e ∧ e * t = t * e := by
  rcases he with rfl | rfl | rfl | rfl
  · simp
  · exact ⟨rfl, hc⟩
  · exact ⟨hc.symm, rfl⟩
  · refine ⟨?_, ?_⟩
    · rw [mul_assoc, ← hc]
    · rw [← mul_assoc t, ← hc]

theorem inE_comm {α t e f : G} (hc : α * t = t * α) (he : InE α t e) (hf : InE α t f) :
    e * f = f * e :=
  comm_E (inE_cent hc he).1 (inE_cent hc he).2 hf

theorem inE_conj {ζ α t e : G} (hζζ : ζ * ζ = 1) (htt : t * t = 1) (hζα : ζ * α = α * t * ζ) (hζt : ζ * t = t * ζ)
    (he : InE α t e) : InE α t (ζ * e * ζ) := by
  have hsplit : ∀ x y : G, ζ * (x * y) * ζ = ζ * x * ζ * (ζ * y * ζ) := by
    intro x y
    simp only [mul_assoc]
    rw [← mul_assoc ζ ζ, hζζ, one_mul]
  have hα : ζ * α * ζ = α * t := by rw [hζα, mul_assoc, hζζ, mul_one]
  have ht : ζ * t * ζ = t := by rw [hζt, mul_assoc, hζζ, mul_one]
  rcases he with rfl | rfl | rfl | rfl
  · left
    rw [mul_one, hζζ]
  · exact Or.inr (Or.inr (Or.inr hα))
  · exact Or.inr (Or.inr (Or.inl ht))
  · right
    left
    rw [hsplit, hα, ht, mul_assoc, htt, mul_one]

theorem tab_t {ζ α t : G} (hζζ : ζ * ζ = 1) (hαα : α * α = 1) (hζα : ζ * α = α * t * ζ) :
    α * ζ * (α * ζ) = t := by
  calc α * ζ * (α * ζ) = α * (ζ * α) * ζ := by simp only [mul_assoc]
    _ = α * (α * t * ζ) * ζ := by rw [hζα]
    _ = α * α * t * (ζ * ζ) := by simp only [mul_assoc]
    _ = t := by rw [hαα, hζζ, one_mul, mul_one]

theorem rel_coset {x y c e f : G} (hey : e * y = y * e) (hxf : x * f = f * x) (hef : e * f = f * e)
    (h : x * y = c * (y * x)) : x * e * (y * f) = c * (y * f * (x * e)) := by
  calc x * e * (y * f) = x * (e * y) * f := by simp only [mul_assoc]
    _ = x * (y * e) * f := by rw [hey]
    _ = x * y * (e * f) := by simp only [mul_assoc]
    _ = c * (y * x) * (f * e) := by rw [h, hef]
    _ = c * (y * (x * f) * e) := by simp only [mul_assoc]
    _ = c * (y * (f * x) * e) := by rw [hxf]
    _ = c * (y * f * (x * e)) := by simp only [mul_assoc]

end E

def TabIn (ζ α t g₁ g₂ h₁ h₂ : Pt) : Prop :=
  (ζ ∈ Sig ∧ α ∈ Sig ∧ t ∈ Sig ∧ g₁ ∈ Sig ∧ g₂ ∈ Sig ∧ h₁ ∈ Sig ∧ h₂ ∈ Sig) ∧
    TabR ζ α t g₁ g₂ h₁ h₂

theorem tabIn_conj {s : Pt} (hs : s ∈ Sig) {ζ α t g₁ g₂ h₁ h₂ : Pt}
    (h : TabIn ζ α t g₁ g₂ h₁ h₂) :
    TabIn (s * ζ * s⁻¹) (s * α * s⁻¹) (s * t * s⁻¹) (s * g₁ * s⁻¹) (s * g₂ * s⁻¹)
      (s * h₁ * s⁻¹) (s * h₂ * s⁻¹) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hR⟩ := h
  have hm : ∀ {x : Pt}, x ∈ Sig → s * x * s⁻¹ ∈ Sig := fun hx =>
    mul_mem (mul_mem hs hx) (inv_mem hs)
  refine ⟨⟨hm h1, hm h2, hm h3, hm h4, hm h5, hm h6, hm h7⟩, ?_⟩
  have := TabR_map (MulAut.conj s).toMonoidHom (MulAut.conj s).injective hR
  simpa [MulAut.conj_apply] using this

section Main

variable {TB one : Nat}

theorem eqK {x y : Nat} (hx : x < 2048) (hy : y < 2048) (h : rk x = rk y) : Nat.beq x y = true :=
  beq_eq_true.2 (rk_inj hx hy h)

theorem canon_min (hT : tbOK TB one = true) (hp : p0Ok () = true) {a T A G : Nat}
    (ha : a < 2048) (hT2 : T < 2048) (hA : A < 2048) (hG : G < 2048) {α t : Pt}
    (hra : rk a = α) (hrT : rk T = t) (hrA : rk A = α * t) (hαα : α * α = 1) (htt : t * t = 1)
    (hα1 : α ≠ 1) (ht1 : t ≠ 1) (hαt : α ≠ t) (hc : α * t = t * α) :
    ∃ m < 2048, canon TB a T A m = true ∧ ∃ e, InE α t e ∧ rk m = rk G * e := by
  have h1 : mulK TB G a < 2048 := mulK_lt hT hp hG ha
  have h2 : mulK TB G T < 2048 := mulK_lt hT hp hG hT2
  have h3 : mulK TB G A < 2048 := mulK_lt hT hp hG hA
  have hfour : ∀ y < 2048, ∀ e, InE α t e → rk y = rk G * e →
      y = G ∨ y = mulK TB G a ∨ y = mulK TB G T ∨ y = mulK TB G A := by
    intro y hy e he hye
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl (rk_inj hy hG (by rw [hye, mul_one]))
    · exact Or.inr (Or.inl (rk_inj hy h1 (by rw [hye, rk_mulK hT hp hG ha, hra])))
    · exact Or.inr (Or.inr (Or.inl (rk_inj hy h2 (by rw [hye, rk_mulK hT hp hG hT2, hrT]))))
    · exact Or.inr (Or.inr (Or.inr (rk_inj hy h3 (by rw [hye, rk_mulK hT hp hG hA, hrA]))))
  obtain ⟨m, hm⟩ : ∃ m, m = min (min G (mulK TB G a)) (min (mulK TB G T) (mulK TB G A)) :=
    ⟨_, rfl⟩
  have hmle : ∀ y < 2048, ∀ e, InE α t e → rk y = rk G * e → m ≤ y := by
    intro y hy e he hye
    rcases hfour y hy e he hye with rfl | rfl | rfl | rfl <;> omega
  have hm4 : m = G ∨ m = mulK TB G a ∨ m = mulK TB G T ∨ m = mulK TB G A := by omega
  have hmE : m < 2048 ∧ ∃ e, InE α t e ∧ rk m = rk G * e := by
    rcases hm4 with h | h | h | h <;> rw [h]
    · exact ⟨hG, 1, Or.inl rfl, (mul_one _).symm⟩
    · exact ⟨h1, α, Or.inr (Or.inl rfl), by rw [rk_mulK hT hp hG ha, hra]⟩
    · exact ⟨h2, t, Or.inr (Or.inr (Or.inl rfl)), by rw [rk_mulK hT hp hG hT2, hrT]⟩
    · exact ⟨h3, α * t, Or.inr (Or.inr (Or.inr rfl)), by rw [rk_mulK hT hp hG hA, hrA]⟩
  obtain ⟨hm2, e, he, hme⟩ := hmE
  have hlt : ∀ y < 2048, InE α t (e * rk y) → rk y ≠ 1 → Nat.blt m (mulK TB m y) = true := by
    intro y hy hey hy1
    have hmy := mulK_lt hT hp hm2 hy
    have hr : rk (mulK TB m y) = rk G * (e * rk y) := by
      rw [rk_mulK hT hp hm2 hy, hme, mul_assoc]
    have hle := hmle _ hmy _ hey hr
    have hne : m ≠ mulK TB m y := by
      intro h
      apply hy1
      have h' : rk m = rk (mulK TB m y) := by rw [← h]
      rw [rk_mulK hT hp hm2 hy] at h'
      exact mul_eq_left.1 h'.symm
    exact blt_eq_true.2 (by omega)
  have hat1 : α * t ≠ 1 := fun h =>
    hαt ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right htt))
  have hE := inE_mul hαα htt hc he
  refine ⟨m, hm2, ?_, e, he, hme⟩
  unfold canon
  rw [andB_eq_true, andB_eq_true]
  refine ⟨hlt a ha (by rw [hra]; exact hE.1) (by rw [hra]; exact hα1),
    hlt T hT2 (by rw [hrT]; exact hE.2.1) (by rw [hrT]; exact ht1),
    hlt A hA (by rw [hrA]; exact hE.2.2) (by rw [hrA]; exact hat1)⟩

theorem rk_zmz (hT : tbOK TB one = true) (hp : p0Ok () = true) {z m : Nat} (hz : z < 2048)
    (hm : m < 2048) {g e : Pt} (hme : rk m = g * e) (hζζ : rk z * rk z = 1) :
    rk (mulK TB (mulK TB z m) z) = rk z * g * rk z * (rk z * e * rk z) := by
  rw [rk_mulK hT hp (mulK_lt hT hp hz hm) hz, rk_mulK hT hp hz hm, hme]
  simp only [mul_assoc]
  rw [← mul_assoc (rk z) (rk z), hζζ, one_mul]

theorem mem_cands (hT : tbOK TB one = true) (hp : p0Ok () = true) {RT : List (Nat × List Nat)}
    (hR : rtOK TB RT = true) {z a T A G : Nat} (hz : z < 2048) (ha : a < 2048) (hT2 : T < 2048)
    (hA : A < 2048) (hG : G < 2048) {α t : Pt} (hra : rk a = α) (hrT : rk T = t)
    (hrA : rk A = α * t) (hζζ : rk z * rk z = 1) (hαα : α * α = 1) (htt : t * t = 1)
    (hα1 : α ≠ 1) (ht1 : t ≠ 1) (hαt : α ≠ t) (hc : α * t = t * α)
    (hζα : rk z * α = α * t * rk z) (hζt : rk z * t = t * rk z)
    (hgα : rk G * α = α * rk G) (hgt : rk G * t = t * rk G)
    (hsq : rk G * rk G = 1 ∨ rk G * rk G = t)
    (hhα : rk z * rk G * rk z * α = α * (rk z * rk G * rk z))
    (hht : rk z * rk G * rk z * t = t * (rk z * rk G * rk z))
    (hgh : rk G * (rk z * rk G * rk z) = rk z * rk G * rk z * rk G) :
    ∃ m < 2048, m ∈ filterL (appL (rootsOf RT one) (rootsOf RT T))
      (fun c => andB (canon TB a T A c) (dOK TB z a T c)) ∧ ∃ e, InE α t e ∧ rk m = rk G * e := by
  obtain ⟨m, hm, hcan, e, he, hme⟩ :=
    canon_min hT hp ha hT2 hA hG hra hrT hrA hαα htt hα1 ht1 hαt hc
  obtain ⟨hone, hrone⟩ := rk_one hT hp
  have hmm : rk (mulK TB m m) = rk G * rk G := by
    rw [rk_mulK hT hp hm hm, hme]
    calc rk G * e * (rk G * e) = rk G * (e * rk G) * e := by simp only [mul_assoc]
      _ = rk G * (rk G * e) * e := by rw [comm_E hgα hgt he]
      _ = rk G * rk G * (e * e) := by simp only [mul_assoc]
      _ = rk G * rk G := by rw [inE_sq hαα htt hc he, mul_one]
  have hroot : m ∈ appL (rootsOf RT one) (rootsOf RT T) := by
    rw [appL_eq, List.mem_append]
    have hr := rtOK_sound hR m hm
    rcases hsq with h | h
    · left
      rwa [rk_inj (mulK_lt hT hp hm hm) hone (by rw [hmm, h, hrone])] at hr
    · right
      rwa [rk_inj (mulK_lt hT hp hm hm) hT2 (by rw [hmm, h, hrT])] at hr
  refine ⟨m, hm, ?_, e, he, hme⟩
  rw [filterL_eq, List.mem_filter]
  refine ⟨hroot, ?_⟩
  rw [andB_eq_true]
  refine ⟨hcan, ?_⟩
  unfold dOK
  simp only [letB_eq, andB_eq_true]
  have hcm := inE_cent hc he
  have hmα : rk m * α = α * rk m := by
    rw [hme, mul_assoc, hcm.1, ← mul_assoc, hgα, mul_assoc]
  have hmt : rk m * t = t * rk m := by
    rw [hme, mul_assoc, hcm.2, ← mul_assoc, hgt, mul_assoc]
  have hzm := mulK_lt hT hp (mulK_lt hT hp hz hm) hz
  refine ⟨eqK (mulK_lt hT hp hm ha) (mulK_lt hT hp ha hm)
      (by rw [rk_mulK hT hp hm ha, rk_mulK hT hp ha hm, hra]; exact hmα),
    eqK (mulK_lt hT hp hm hT2) (mulK_lt hT hp hT2 hm)
      (by rw [rk_mulK hT hp hm hT2, rk_mulK hT hp hT2 hm, hrT]; exact hmt),
    eqK (mulK_lt hT hp hm hzm) (mulK_lt hT hp hzm hm) ?_⟩
  rw [rk_mulK hT hp hm hzm, rk_mulK hT hp hzm hm, rk_zmz hT hp hz hm hme hζζ, hme]
  have he' := inE_conj hζζ htt hζα hζt he
  have := rel_coset (c := 1) (comm_E hhα hht he).symm (comm_E hgα hgt he') (inE_comm hc he he')
    (by rw [one_mul]; exact hgh)
  rwa [one_mul] at this

theorem no_tab_row (hT : tbOK TB one = true) (hp : p0Ok () = true) {RT : List (Nat × List Nat)}
    (hR : rtOK TB RT = true) {z a : Nat} (hz : z < 2048) (ha : a < 2048)
    (hrow : rowOK TB RT one z a = true) {t g₁ g₂ h₁ h₂ : Pt} (hg₁ : g₁ ∈ Sig) (hg₂ : g₂ ∈ Sig)
    (h : TabR (rk z) (rk a) t g₁ g₂ h₁ h₂) : False := by
  obtain ⟨hζζ, hαα, htt, hα1, ht1, hαt, hc, hζt, hζα, hh1ζ, hh2ζ, ⟨hg1α, hg1t⟩,
    ⟨hg2α, hg2t⟩, ⟨hh1α, hh1t⟩, ⟨hh2α, hh2t⟩, hsq1, hsq2, hgg, -, hgh, -, hg1h1, hg2h2⟩ := h
  have hh1 : h₁ = rk z * g₁ * rk z := by rw [← hh1ζ, mul_assoc, hζζ, mul_one]
  have hh2 : h₂ = rk z * g₂ * rk z := by rw [← hh2ζ, mul_assoc, hζζ, mul_one]
  subst hh1 hh2
  obtain ⟨G1, hG1, rfl⟩ := rk_surj hg₁
  obtain ⟨G2, hG2, rfl⟩ := rk_surj hg₂
  unfold rowOK at hrow
  simp only [letB_eq] at hrow
  have haz := mulK_lt hT hp ha hz
  have hT2 := mulK_lt hT hp haz haz
  have hA2 := mulK_lt hT hp ha hT2
  have hrT : rk (mulK TB (mulK TB a z) (mulK TB a z)) = t := by
    rw [rk_mulK hT hp haz haz, rk_mulK hT hp ha hz]
    exact tab_t hζζ hαα hζα
  have hrA : rk (mulK TB a (mulK TB (mulK TB a z) (mulK TB a z))) = rk a * t := by
    rw [rk_mulK hT hp ha hT2, hrT]
  obtain ⟨m1, hm1, hmem1, e1, he1, hme1⟩ := mem_cands hT hp hR hz ha hT2 hA2 hG1 rfl hrT hrA
    hζζ hαα htt hα1 ht1 hαt hc hζα hζt hg1α hg1t hsq1 hh1α hh1t hg1h1
  obtain ⟨m2, hm2, hmem2, e2, he2, hme2⟩ := mem_cands hT hp hR hz ha hT2 hA2 hG2 rfl hrT hrA
    hζζ hαα htt hα1 ht1 hαt hc hζα hζt hg2α hg2t hsq2 hh2α hh2t hg2h2
  unfold pairsOK at hrow
  rw [allL_eq_true] at hrow
  have hrow1 := hrow m1 hmem1
  rw [allL_eq_true] at hrow1
  have hrow2 := hrow1 m2 hmem2
  simp only [letB_eq, notB_eq_true] at hrow2
  have hzm := mulK_lt hT hp (mulK_lt hT hp hz hm2) hz
  have he2' := inE_conj hζζ htt hζα hζt he2
  have hpair : andB (Nat.beq (mulK TB m1 m2)
      (mulK TB (mulK TB a (mulK TB (mulK TB a z) (mulK TB a z))) (mulK TB m2 m1)))
      (Nat.beq (mulK TB m1 (mulK TB (mulK TB z m2) z))
        (mulK TB (mulK TB (mulK TB a z) (mulK TB a z))
          (mulK TB (mulK TB (mulK TB z m2) z) m1))) = true := by
    rw [andB_eq_true]
    refine ⟨eqK (mulK_lt hT hp hm1 hm2) (mulK_lt hT hp hA2 (mulK_lt hT hp hm2 hm1)) ?_,
      eqK (mulK_lt hT hp hm1 hzm) (mulK_lt hT hp hT2 (mulK_lt hT hp hzm hm1)) ?_⟩
    · rw [rk_mulK hT hp hm1 hm2, rk_mulK hT hp hA2 (mulK_lt hT hp hm2 hm1),
        rk_mulK hT hp hm2 hm1, hrA, hme1, hme2]
      exact rel_coset (comm_E hg2α hg2t he1).symm (comm_E hg1α hg1t he2) (inE_comm hc he1 he2)
        hgg
    · rw [rk_mulK hT hp hm1 hzm, rk_mulK hT hp hT2 (mulK_lt hT hp hzm hm1),
        rk_mulK hT hp hzm hm1, hrT, rk_zmz hT hp hz hm2 hme2 hζζ, hme1]
      exact rel_coset (comm_E hh2α hh2t he1).symm (comm_E hg1α hg1t he2')
        (inE_comm hc he1 he2') hgh
  rw [hrow2] at hpair
  exact Bool.false_ne_true hpair

theorem tab_zeta (hT : tbOK TB one = true) (hp : p0Ok () = true) {RT : List (Nat × List Nat)}
    (hR : rtOK TB RT = true) {ZA : List (Nat × List Nat)} {ZC : List (Nat × Nat)}
    (hZ : zOK TB RT one ZA ZC = true) {AC : List (List (Nat × Nat))} {n : Nat}
    (hA : zaOK TB RT one ZA AC n = true) {ζ α t g₁ g₂ h₁ h₂ : Pt} (h : TabIn ζ α t g₁ g₂ h₁ h₂) :
    ∃ z al, (z, al) ∈ ZA ∧ ∃ α' t' g₁' g₂' h₁' h₂', TabIn (rk z) α' t' g₁' g₂' h₁' h₂' := by
  have h0 := h
  obtain ⟨⟨hz, -⟩, hζζ, -, -, -, ht1, -, -, -, hζα, -⟩ := h0
  obtain ⟨xz, hxz, rfl⟩ := rk_surj hz
  obtain ⟨hone, hrone⟩ := rk_one hT hp
  have hz1 : xz ≠ one := by
    intro h1
    apply ht1
    rw [h1, hrone, one_mul, mul_one] at hζα
    exact mul_eq_left.1 hζα.symm
  have hsq : mulK TB xz xz = one :=
    rk_inj (mulK_lt hT hp hxz hxz) hone (by rw [rk_mulK hT hp hxz hxz, hζζ, hrone])
  have hroot := rtOK_sound hR xz hxz
  rw [hsq] at hroot
  obtain ⟨p, hrec⟩ := zGo_sound hZ xz hroot
  unfold zRec at hrec
  rw [orB_eq_true, beq_false hz1, andB_eq_true, andB_eq_true, blt_eq_true] at hrec
  obtain ⟨hkey, hs, hsz⟩ := hrec.resolve_left Bool.false_ne_true
  obtain ⟨al, hal⟩ := memKey_sound hkey
  refine ⟨p.1, al, hal, ?_⟩
  have hp1 : p.1 < 2048 := (zaGo_sound (zaGo_of_zaOK hA) (p.1, al) hal).1
  have hsz' : rk p.2 * rk xz * (rk p.2)⁻¹ = rk p.1 := by
    have := congrArg rk (beq_eq_true.1 hsz)
    rw [rk_mulK hT hp hs hxz, rk_mulK hT hp hp1 hs] at this
    rw [this, mul_inv_cancel_right]
  have hc := tabIn_conj (rk_mem hs) h
  rw [hsz'] at hc
  exact ⟨_, _, _, _, _, _, hc⟩

theorem tab_alpha (hT : tbOK TB one = true) (hp : p0Ok () = true) {RT : List (Nat × List Nat)}
    (hR : rtOK TB RT = true) {z : Nat} {al : List Nat} (hz : z < 2048)
    (hal : ∀ r ∈ al, r < 2048)
    (hrec : ∀ x ∈ filterL (rootsOf RT one) (aCand TB one z), ∃ q, aRec TB z al x q = true)
    {α t g₁ g₂ h₁ h₂ : Pt} (h : TabIn (rk z) α t g₁ g₂ h₁ h₂) :
    ∃ r ∈ al, ∃ t' g₁' g₂' h₁' h₂', TabIn (rk z) (rk r) t' g₁' g₂' h₁' h₂' := by
  have h0 := h
  obtain ⟨⟨-, ha, -⟩, hζζ, hαα, htt, -, ht1, hαt, hc, hζt, hζα, -⟩ := h0
  obtain ⟨xa, hxa, rfl⟩ := rk_surj ha
  obtain ⟨hone, hrone⟩ := rk_one hT hp
  have haz := mulK_lt hT hp hxa hz
  have hT2 := mulK_lt hT hp haz haz
  have hrT : rk (mulK TB (mulK TB xa z) (mulK TB xa z)) = t := by
    rw [rk_mulK hT hp haz haz, rk_mulK hT hp hxa hz]
    exact tab_t hζζ hαα hζα
  have hsq : mulK TB xa xa = one :=
    rk_inj (mulK_lt hT hp hxa hxa) hone (by rw [rk_mulK hT hp hxa hxa, hαα, hrone])
  have hroot : xa ∈ rootsOf RT one := by
    have := rtOK_sound hR xa hxa
    rwa [hsq] at this
  have hcand : aCand TB one z xa = true := by
    unfold aCand
    simp only [letB_eq, andB_eq_true, notB_eq_true]
    refine ⟨beq_false fun h1 => ht1 (by rw [← hrT, h1, hrone]),
      beq_false fun h1 => hαt (by rw [← hrT, h1]),
      eqK (mulK_lt hT hp hT2 hT2) hone (by rw [rk_mulK hT hp hT2 hT2, hrT, htt, hrone]),
      eqK (mulK_lt hT hp hxa hT2) (mulK_lt hT hp hT2 hxa)
        (by rw [rk_mulK hT hp hxa hT2, rk_mulK hT hp hT2 hxa, hrT]; exact hc),
      eqK (mulK_lt hT hp hz hT2) (mulK_lt hT hp hT2 hz)
        (by rw [rk_mulK hT hp hz hT2, rk_mulK hT hp hT2 hz, hrT]; exact hζt)⟩
  obtain ⟨q, hq⟩ := hrec xa (by rw [filterL_eq, List.mem_filter]; exact ⟨hroot, hcand⟩)
  unfold aRec at hq
  simp only [andB_eq_true, memN_eq_true, blt_eq_true, beq_eq_true] at hq
  obtain ⟨hr, hs, hsz, hsa⟩ := hq
  have hr2 := hal _ hr
  have hz' : rk q.2 * rk z * (rk q.2)⁻¹ = rk z := by
    have := congrArg rk hsz
    rw [rk_mulK hT hp hs hz, rk_mulK hT hp hz hs] at this
    rw [this, mul_inv_cancel_right]
  have ha' : rk q.2 * rk xa * (rk q.2)⁻¹ = rk q.1 := by
    have := congrArg rk hsa
    rw [rk_mulK hT hp hs hxa, rk_mulK hT hp hr2 hs] at this
    rw [this, mul_inv_cancel_right]
  have hc' := tabIn_conj (rk_mem hs) h
  rw [hz', ha'] at hc'
  exact ⟨q.1, hr, _, _, _, _, _, hc'⟩

theorem noTabSig_of_checks {RT : List (Nat × List Nat)} {ZA : List (Nat × List Nat)}
    {ZC : List (Nat × Nat)} {AC : List (List (Nat × Nat))} {n : Nat}
    (hT : tbOK TB one = true) (hp : p0Ok () = true) (hR : rtOK TB RT = true)
    (hZ : zOK TB RT one ZA ZC = true) (hA : zaOK TB RT one ZA AC n = true)
    (hrows : ∀ k, 0 ≤ k → k < n → ∃ z a, rowChk TB RT one ZA k z a = true) : NoTabSig := by
  intro ζ α t g₁ g₂ h₁ h₂ hζ hα ht hg₁ hg₂ hh₁ hh₂ hR'
  obtain ⟨z, al, hzal, α', t', g₁', g₂', h₁', h₂', h1⟩ :=
    tab_zeta hT hp hR hZ hA (⟨⟨hζ, hα, ht, hg₁, hg₂, hh₁, hh₂⟩, hR'⟩ :
      TabIn ζ α t g₁ g₂ h₁ h₂)
  obtain ⟨hz, hal, hrec⟩ := zaGo_sound (zaGo_of_zaOK hA) (z, al) hzal
  obtain ⟨r, hr, t'', g₁'', g₂'', h₁'', h₂'', h2⟩ := tab_alpha hT hp hR hz hal hrec h1
  obtain ⟨⟨-, -, -, hG1, hG2, -⟩, hR''⟩ := h2
  exact no_tab_row hT hp hR hz (hal r hr) (rowOK_of_checks hA hrows hzal hr) hG1 hG2 hR''

end Main

end CFSG.KC.TS8WrK
