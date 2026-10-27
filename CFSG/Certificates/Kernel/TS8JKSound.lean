module

public import CFSG.Certificates.Kernel.TS8WrKSound2
public import Certificates.Data.Kernel.TS8JK
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.TS8JKSound

open CFSG.KC.TS8JK
open CFSG.KC.TS8WrK (andB orB notB letB allN allL memN filterL appL rootsOf sumLen memKey
  andB_eq_true letB_eq allN_eq_true orB_eq_true notB_eq_true beq_eq_true beq_false blt_eq_true
  allL_eq_true memN_eq_true filterL_eq appL_eq memKey_sound rootsOf_of_mem sumLen_eq tab_t
  rel_coset)
open CFSG.EvenSporadicStandard.Fin76b (OuterTable)
open CFSG.EvenSporadicStandard.Fin76b.TS8Wr (TabR TabR_map tabR_of_outerTable)
open CFSG.KS.Raw.Orb (PRep prep_pcomp prep_pidn)

theorem f8_lt (x i : Nat) : f8 x i < 256 := by
  unfold f8
  exact Nat.lt_succ_of_le Nat.and_le_right

theorem mK_lt (M : Nat → Nat) (a b : Nat) : mK M a b < 256 := f8_lt _ _

section Lists

variable {M : Nat → Nat}

theorem rootsGo_sound {s : Nat} : ∀ {l : List Nat} {lo : Nat}, rootsGo M s l lo = true →
    l.Pairwise (· < ·) ∧ ∀ r ∈ l, lo ≤ r ∧ r < 256 ∧ mK M r r = s
  | [], _, _ => ⟨List.Pairwise.nil, fun r hr => by simp at hr⟩
  | r :: l, lo, h => by
    have h' : andB (Nat.ble lo r) (andB (Nat.blt r 256) (andB (Nat.beq (mK M r r) s)
        (rootsGo M s l (Nat.succ r)))) = true := h
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

theorem rtGo_sound : ∀ {RT : List (Nat × List Nat)} {lo : Nat}, rtGo M RT lo = true →
    RT.Pairwise (fun p q => p.1 < q.1) ∧ ∀ p ∈ RT, lo ≤ p.1 ∧ p.2.Pairwise (· < ·) ∧
      ∀ r ∈ p.2, r < 256 ∧ mK M r r = p.1
  | [], _, _ => ⟨List.Pairwise.nil, fun p hp => by simp at hp⟩
  | p :: RT, lo, h => by
    have h' : andB (Nat.ble lo p.1) (andB (rootsGo M p.1 p.2 0)
        (rtGo M RT (Nat.succ p.1))) = true := h
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

theorem rtOK_sound {RT : List (Nat × List Nat)} (h : rtOK M RT = true) :
    ∀ c < 256, c ∈ rootsOf RT (mK M c c) := by
  intro c hc
  have h' := andB_eq_true.1 h
  obtain ⟨hpw, hall⟩ := rtGo_sound h'.2
  have hlen : (RT.flatMap Prod.snd).length = 256 := by
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
  have hsub : (RT.flatMap Prod.snd).toFinset = Finset.range 256 := by
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

theorem zGo_sound {ZA : List (Nat × List Nat)} :
    ∀ {xs : List Nat} {zc : List (Nat × Nat)}, zGo M ZA xs zc = true →
      ∀ x ∈ xs, ∃ p, zRec M ZA x p = true
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], h, _, _ => Bool.noConfusion (h : false = true)
  | y :: xs, p :: zc, h, x, hx => by
    have h' : andB (zRec M ZA y p) (zGo M ZA xs zc) = true := h
    rw [andB_eq_true] at h'
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨p, h'.1⟩
    · exact zGo_sound h'.2 x hx

theorem aGo_sound {z : Nat} {al : List Nat} :
    ∀ {xs : List Nat} {ac : List (Nat × Nat)}, aGo M z al xs ac = true →
      ∀ x ∈ xs, ∃ p, aRec M z al x p = true
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], h, _, _ => Bool.noConfusion (h : false = true)
  | y :: xs, p :: ac, h, x, hx => by
    have h' : andB (aRec M z al y p) (aGo M z al xs ac) = true := h
    rw [andB_eq_true] at h'
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨p, h'.1⟩
    · exact aGo_sound h'.2 x hx

theorem zaGo_sound {RT : List (Nat × List Nat)} :
    ∀ {ZA : List (Nat × List Nat)} {AC : List (List (Nat × Nat))}, zaGo M RT ZA AC = true →
      ∀ p ∈ ZA, p.1 < 256 ∧ (∀ r ∈ p.2, r < 256) ∧
        ∀ x ∈ filterL (rootsOf RT 0) (aCand M p.1), ∃ q, aRec M p.1 p.2 x q = true
  | [], _, _, p, hp => by simp at hp
  | _ :: _, [], h, _, _ => Bool.noConfusion (h : false = true)
  | q :: ZA, acl :: AC, h, p, hp => by
    have h' : andB (Nat.blt q.1 256) (andB (allL q.2 fun r => Nat.blt r 256)
        (andB (aGo M q.1 q.2 (filterL (rootsOf RT 0) (aCand M q.1)) acl)
          (zaGo M RT ZA AC))) = true := h
    simp only [andB_eq_true, allL_eq_true, blt_eq_true] at h'
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨h'.1, h'.2.1, aGo_sound h'.2.2.1⟩
    · exact zaGo_sound h'.2.2.2 p hp

theorem rowsOK_sound {RT : List (Nat × List Nat)} {zc ac : Nat} {ZA : List (Nat × List Nat)}
    (h : rowsOK M RT zc ac ZA = true) : ∀ p ∈ ZA, ∀ a ∈ p.2, rowOK M RT zc ac p.1 a = true := by
  induction ZA with
  | nil =>
    intro p hp
    simp at hp
  | cons q ZA ih =>
    have h' : andB (allL q.2 fun a => rowOK M RT zc ac q.1 a) (rowsOK M RT zc ac ZA) = true := h
    rw [andB_eq_true, allL_eq_true] at h'
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h'.1
    · exact ih h'.2 p hp

end Lists

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

theorem inE_conj {ζ α t e : G} (hζζ : ζ * ζ = 1) (htt : t * t = 1) (hζα : ζ * α = α * t * ζ)
    (hζt : ζ * t = t * ζ) (he : InE α t e) : InE α t (ζ * e * ζ) := by
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

end E

structure Mdl {X : Type*} [Group X] (M : Nat → Nat) (Ev : Nat → X) : Prop where
  mul : ∀ {x y : Nat}, x < 256 → y < 256 → Ev (mK M x y) = Ev x * Ev y
  inj : ∀ {x y : Nat}, x < 256 → y < 256 → Ev x = Ev y → x = y
  one : Ev 0 = 1

section Search

variable {X : Type*} [Group X] {M : Nat → Nat} {Ev : Nat → X} {J : Subgroup X}

def TabJ (J : Subgroup X) (ζ α t g₁ g₂ h₁ h₂ : X) : Prop :=
  (ζ ∈ J ∧ α ∈ J ∧ t ∈ J ∧ g₁ ∈ J ∧ g₂ ∈ J ∧ h₁ ∈ J ∧ h₂ ∈ J) ∧ TabR ζ α t g₁ g₂ h₁ h₂

theorem tabJ_conj {s : X} (hs : s ∈ J) {ζ α t g₁ g₂ h₁ h₂ : X}
    (h : TabJ J ζ α t g₁ g₂ h₁ h₂) :
    TabJ J (s * ζ * s⁻¹) (s * α * s⁻¹) (s * t * s⁻¹) (s * g₁ * s⁻¹) (s * g₂ * s⁻¹)
      (s * h₁ * s⁻¹) (s * h₂ * s⁻¹) := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hR⟩ := h
  have hm : ∀ {x : X}, x ∈ J → s * x * s⁻¹ ∈ J := fun hx =>
    J.mul_mem (J.mul_mem hs hx) (J.inv_mem hs)
  refine ⟨⟨hm h1, hm h2, hm h3, hm h4, hm h5, hm h6, hm h7⟩, ?_⟩
  have := TabR_map (MulAut.conj s).toMonoidHom (MulAut.conj s).injective hR
  simpa [MulAut.conj_apply] using this

theorem eqK (hE : Mdl M Ev) {x y : Nat} (hx : x < 256) (hy : y < 256) (h : Ev x = Ev y) :
    Nat.beq x y = true :=
  beq_eq_true.2 (hE.inj hx hy h)

theorem canon_min (hE : Mdl M Ev) {a T A G : Nat}
    (ha : a < 256) (hT2 : T < 256) (hA : A < 256) (hG : G < 256) {α t : X}
    (hra : Ev a = α) (hrT : Ev T = t) (hrA : Ev A = α * t) (hαα : α * α = 1) (htt : t * t = 1)
    (hα1 : α ≠ 1) (ht1 : t ≠ 1) (hαt : α ≠ t) (hc : α * t = t * α) :
    ∃ m < 256, canon M a T A m = true ∧ ∃ e, InE α t e ∧ Ev m = Ev G * e := by
  have h1 : mK M G a < 256 := mK_lt M _ _
  have h2 : mK M G T < 256 := mK_lt M _ _
  have h3 : mK M G A < 256 := mK_lt M _ _
  have hfour : ∀ y < 256, ∀ e, InE α t e → Ev y = Ev G * e →
      y = G ∨ y = mK M G a ∨ y = mK M G T ∨ y = mK M G A := by
    intro y hy e he hye
    rcases he with rfl | rfl | rfl | rfl
    · exact Or.inl (hE.inj hy hG (by rw [hye, mul_one]))
    · exact Or.inr (Or.inl (hE.inj hy h1 (by rw [hye, hE.mul hG ha, hra])))
    · exact Or.inr (Or.inr (Or.inl (hE.inj hy h2 (by rw [hye, hE.mul hG hT2, hrT]))))
    · exact Or.inr (Or.inr (Or.inr (hE.inj hy h3 (by rw [hye, hE.mul hG hA, hrA]))))
  obtain ⟨m, hm⟩ : ∃ m, m = min (min G (mK M G a)) (min (mK M G T) (mK M G A)) :=
    ⟨_, rfl⟩
  have hmle : ∀ y < 256, ∀ e, InE α t e → Ev y = Ev G * e → m ≤ y := by
    intro y hy e he hye
    rcases hfour y hy e he hye with rfl | rfl | rfl | rfl <;> omega
  have hm4 : m = G ∨ m = mK M G a ∨ m = mK M G T ∨ m = mK M G A := by omega
  have hmE : m < 256 ∧ ∃ e, InE α t e ∧ Ev m = Ev G * e := by
    rcases hm4 with h | h | h | h <;> rw [h]
    · exact ⟨hG, 1, Or.inl rfl, (mul_one _).symm⟩
    · exact ⟨h1, α, Or.inr (Or.inl rfl), by rw [hE.mul hG ha, hra]⟩
    · exact ⟨h2, t, Or.inr (Or.inr (Or.inl rfl)), by rw [hE.mul hG hT2, hrT]⟩
    · exact ⟨h3, α * t, Or.inr (Or.inr (Or.inr rfl)), by rw [hE.mul hG hA, hrA]⟩
  obtain ⟨hm2, e, he, hme⟩ := hmE
  have hlt : ∀ y < 256, InE α t (e * Ev y) → Ev y ≠ 1 → Nat.blt m (mK M m y) = true := by
    intro y hy hey hy1
    have hmy := mK_lt M m y
    have hr : Ev (mK M m y) = Ev G * (e * Ev y) := by
      rw [hE.mul hm2 hy, hme, mul_assoc]
    have hle := hmle _ hmy _ hey hr
    have hne : m ≠ mK M m y := by
      intro h
      apply hy1
      have h' : Ev m = Ev (mK M m y) := by rw [← h]
      rw [hE.mul hm2 hy] at h'
      exact mul_eq_left.1 h'.symm
    exact blt_eq_true.2 (by omega)
  have hat1 : α * t ≠ 1 := fun h =>
    hαt ((eq_inv_of_mul_eq_one_left h).trans (inv_eq_of_mul_eq_one_right htt))
  have hE4 := inE_mul hαα htt hc he
  refine ⟨m, hm2, ?_, e, he, hme⟩
  unfold canon
  rw [andB_eq_true, andB_eq_true]
  refine ⟨hlt a ha (by rw [hra]; exact hE4.1) (by rw [hra]; exact hα1),
    hlt T hT2 (by rw [hrT]; exact hE4.2.1) (by rw [hrT]; exact ht1),
    hlt A hA (by rw [hrA]; exact hE4.2.2) (by rw [hrA]; exact hat1)⟩

theorem ev_zmz (hE : Mdl M Ev) {z m : Nat} (hz : z < 256)
    (hm : m < 256) {g e : X} (hme : Ev m = g * e) (hζζ : Ev z * Ev z = 1) :
    Ev (mK M (mK M z m) z) = Ev z * g * Ev z * (Ev z * e * Ev z) := by
  rw [hE.mul (mK_lt M _ _) hz, hE.mul hz hm, hme]
  simp only [mul_assoc]
  rw [← mul_assoc (Ev z) (Ev z), hζζ, one_mul]

theorem mem_cands (hE : Mdl M Ev) {RT : List (Nat × List Nat)}
    (hR : rtOK M RT = true) {z a T A G : Nat} (hz : z < 256) (ha : a < 256) (hT2 : T < 256)
    (hA : A < 256) (hG : G < 256) {α t : X} (hra : Ev a = α) (hrT : Ev T = t)
    (hrA : Ev A = α * t) (hζζ : Ev z * Ev z = 1) (hαα : α * α = 1) (htt : t * t = 1)
    (hα1 : α ≠ 1) (ht1 : t ≠ 1) (hαt : α ≠ t) (hc : α * t = t * α)
    (hζα : Ev z * α = α * t * Ev z) (hζt : Ev z * t = t * Ev z)
    (hgα : Ev G * α = α * Ev G) (hgt : Ev G * t = t * Ev G)
    (hsq : Ev G * Ev G = 1 ∨ Ev G * Ev G = t)
    (hhα : Ev z * Ev G * Ev z * α = α * (Ev z * Ev G * Ev z))
    (hht : Ev z * Ev G * Ev z * t = t * (Ev z * Ev G * Ev z))
    (hgh : Ev G * (Ev z * Ev G * Ev z) = Ev z * Ev G * Ev z * Ev G) :
    ∃ m < 256, m ∈ filterL (appL (rootsOf RT 0) (rootsOf RT T))
      (fun c => andB (canon M a T A c) (dOK M z a T c)) ∧ ∃ e, InE α t e ∧ Ev m = Ev G * e := by
  obtain ⟨m, hm, hcan, e, he, hme⟩ :=
    canon_min hE ha hT2 hA hG hra hrT hrA hαα htt hα1 ht1 hαt hc
  have hone : (0 : Nat) < 256 := by norm_num
  have hrone : Ev 0 = 1 := hE.one
  have hmm : Ev (mK M m m) = Ev G * Ev G := by
    rw [hE.mul hm hm, hme]
    calc Ev G * e * (Ev G * e) = Ev G * (e * Ev G) * e := by simp only [mul_assoc]
      _ = Ev G * (Ev G * e) * e := by rw [comm_E hgα hgt he]
      _ = Ev G * Ev G * (e * e) := by simp only [mul_assoc]
      _ = Ev G * Ev G := by rw [inE_sq hαα htt hc he, mul_one]
  have hroot : m ∈ appL (rootsOf RT 0) (rootsOf RT T) := by
    rw [appL_eq, List.mem_append]
    have hr := rtOK_sound hR m hm
    rcases hsq with h | h
    · left
      rwa [hE.inj (mK_lt M m m) hone (by rw [hmm, h, hrone])] at hr
    · right
      rwa [hE.inj (mK_lt M m m) hT2 (by rw [hmm, h, hrT])] at hr
  refine ⟨m, hm, ?_, e, he, hme⟩
  rw [filterL_eq, List.mem_filter]
  refine ⟨hroot, ?_⟩
  rw [andB_eq_true]
  refine ⟨hcan, ?_⟩
  unfold dOK
  simp only [letB_eq, andB_eq_true]
  have hcm := inE_cent hc he
  have hmα : Ev m * α = α * Ev m := by
    rw [hme, mul_assoc, hcm.1, ← mul_assoc, hgα, mul_assoc]
  have hmt : Ev m * t = t * Ev m := by
    rw [hme, mul_assoc, hcm.2, ← mul_assoc, hgt, mul_assoc]
  have hzm := mK_lt M (mK M z m) z
  refine ⟨eqK hE (mK_lt M _ _) (mK_lt M _ _)
      (by rw [hE.mul hm ha, hE.mul ha hm, hra]; exact hmα),
    eqK hE (mK_lt M _ _) (mK_lt M _ _)
      (by rw [hE.mul hm hT2, hE.mul hT2 hm, hrT]; exact hmt),
    eqK hE (mK_lt M _ _) (mK_lt M _ _) ?_⟩
  rw [hE.mul hm hzm, hE.mul hzm hm, ev_zmz hE hz hm hme hζζ, hme]
  have he' := inE_conj hζζ htt hζα hζt he
  have := rel_coset (c := 1) (comm_E hhα hht he).symm (comm_E hgα hgt he') (inE_comm hc he he')
    (by rw [one_mul]; exact hgh)
  rwa [one_mul] at this

theorem no_tab_row (hE : Mdl M Ev) (hJ : ∀ g, g ∈ J ↔ ∃ k < 256, Ev k = g)
    {RT : List (Nat × List Nat)} (hR : rtOK M RT = true) {zc ac z a : Nat} (hz : z < 256)
    (ha : a < 256) (hrow : rowOK M RT zc ac z a = true) (hne : ¬ (z = zc ∧ a = ac))
    {t g₁ g₂ h₁ h₂ : X} (hg₁ : g₁ ∈ J) (hg₂ : g₂ ∈ J)
    (h : TabR (Ev z) (Ev a) t g₁ g₂ h₁ h₂) : False := by
  obtain ⟨hζζ, hαα, htt, hα1, ht1, hαt, hc, hζt, hζα, hh1ζ, hh2ζ, ⟨hg1α, hg1t⟩,
    ⟨hg2α, hg2t⟩, ⟨hh1α, hh1t⟩, ⟨hh2α, hh2t⟩, hsq1, hsq2, hgg, -, hgh, -, hg1h1, hg2h2⟩ := h
  have hh1 : h₁ = Ev z * g₁ * Ev z := by rw [← hh1ζ, mul_assoc, hζζ, mul_one]
  have hh2 : h₂ = Ev z * g₂ * Ev z := by rw [← hh2ζ, mul_assoc, hζζ, mul_one]
  subst hh1 hh2
  obtain ⟨G1, hG1, rfl⟩ := (hJ _).1 hg₁
  obtain ⟨G2, hG2, rfl⟩ := (hJ _).1 hg₂
  unfold rowOK at hrow
  rw [orB_eq_true] at hrow
  have hrow' := hrow.resolve_left fun h' => hne (by
    rw [andB_eq_true, beq_eq_true, beq_eq_true] at h'
    exact h')
  simp only [letB_eq] at hrow'
  have haz := mK_lt M a z
  have hT2 := mK_lt M (mK M a z) (mK M a z)
  have hA2 := mK_lt M a (mK M (mK M a z) (mK M a z))
  have hrT : Ev (mK M (mK M a z) (mK M a z)) = t := by
    rw [hE.mul haz haz, hE.mul ha hz]
    exact tab_t hζζ hαα hζα
  have hrA : Ev (mK M a (mK M (mK M a z) (mK M a z))) = Ev a * t := by
    rw [hE.mul ha hT2, hrT]
  obtain ⟨m1, hm1, hmem1, e1, he1, hme1⟩ := mem_cands hE hR hz ha hT2 hA2 hG1 rfl hrT hrA
    hζζ hαα htt hα1 ht1 hαt hc hζα hζt hg1α hg1t hsq1 hh1α hh1t hg1h1
  obtain ⟨m2, hm2, hmem2, e2, he2, hme2⟩ := mem_cands hE hR hz ha hT2 hA2 hG2 rfl hrT hrA
    hζζ hαα htt hα1 ht1 hαt hc hζα hζt hg2α hg2t hsq2 hh2α hh2t hg2h2
  unfold pairsOK at hrow'
  rw [allL_eq_true] at hrow'
  have hrow1 := hrow' m1 hmem1
  rw [allL_eq_true] at hrow1
  have hrow2 := hrow1 m2 hmem2
  simp only [letB_eq, notB_eq_true] at hrow2
  have hzm := mK_lt M (mK M z m2) z
  have he2' := inE_conj hζζ htt hζα hζt he2
  have hpair : andB (Nat.beq (mK M m1 m2)
      (mK M (mK M a (mK M (mK M a z) (mK M a z))) (mK M m2 m1)))
      (Nat.beq (mK M m1 (mK M (mK M z m2) z))
        (mK M (mK M (mK M a z) (mK M a z))
          (mK M (mK M (mK M z m2) z) m1))) = true := by
    rw [andB_eq_true]
    refine ⟨eqK hE (mK_lt M _ _) (mK_lt M _ _) ?_, eqK hE (mK_lt M _ _) (mK_lt M _ _) ?_⟩
    · rw [hE.mul hm1 hm2, hE.mul hA2 (mK_lt M _ _), hE.mul hm2 hm1, hrA, hme1, hme2]
      exact rel_coset (comm_E hg2α hg2t he1).symm (comm_E hg1α hg1t he2) (inE_comm hc he1 he2)
        hgg
    · rw [hE.mul hm1 hzm, hE.mul hT2 (mK_lt M _ _), hE.mul hzm hm1, hrT,
        ev_zmz hE hz hm2 hme2 hζζ, hme1]
      exact rel_coset (comm_E hh2α hh2t he1).symm (comm_E hg1α hg1t he2')
        (inE_comm hc he1 he2') hgh
  rw [hrow2] at hpair
  exact Bool.false_ne_true hpair

theorem tab_zeta (hE : Mdl M Ev) (hJ : ∀ g, g ∈ J ↔ ∃ k < 256, Ev k = g)
    {RT : List (Nat × List Nat)} (hR : rtOK M RT = true) {ZA : List (Nat × List Nat)}
    {ZC : List (Nat × Nat)} (hZ : zOK M RT ZA ZC = true) {AC : List (List (Nat × Nat))}
    (hA : zaGo M RT ZA AC = true) {ζ α t g₁ g₂ h₁ h₂ : X} (h : TabJ J ζ α t g₁ g₂ h₁ h₂) :
    ∃ z al, (z, al) ∈ ZA ∧ ∃ s ∈ J, s * ζ * s⁻¹ = Ev z ∧
      ∃ α' t' g₁' g₂' h₁' h₂', s * α * s⁻¹ = α' ∧ TabJ J (Ev z) α' t' g₁' g₂' h₁' h₂' := by
  have h0 := h
  obtain ⟨⟨hz, -⟩, hζζ, -, -, -, ht1, -, -, -, hζα, -⟩ := h0
  obtain ⟨xz, hxz, rfl⟩ := (hJ _).1 hz
  have hrone : Ev 0 = 1 := hE.one
  have hz1 : xz ≠ 0 := by
    intro h1
    apply ht1
    rw [h1, hrone, one_mul, mul_one] at hζα
    exact mul_eq_left.1 hζα.symm
  have hsq : mK M xz xz = 0 :=
    hE.inj (mK_lt M _ _) (by norm_num) (by rw [hE.mul hxz hxz, hζζ, hrone])
  have hroot := rtOK_sound hR xz hxz
  rw [hsq] at hroot
  obtain ⟨p, hrec⟩ := zGo_sound hZ xz hroot
  unfold zRec at hrec
  rw [orB_eq_true, beq_false hz1, andB_eq_true, andB_eq_true, blt_eq_true] at hrec
  obtain ⟨hkey, hs, hsz⟩ := hrec.resolve_left Bool.false_ne_true
  obtain ⟨al, hal⟩ := memKey_sound hkey
  have hp1 : p.1 < 256 := (zaGo_sound hA (p.1, al) hal).1
  have hsz' : Ev p.2 * Ev xz * (Ev p.2)⁻¹ = Ev p.1 := by
    have := congrArg Ev (beq_eq_true.1 hsz)
    rw [hE.mul hs hxz, hE.mul hp1 hs] at this
    rw [this, mul_inv_cancel_right]
  have hsJ : Ev p.2 ∈ J := (hJ _).2 ⟨p.2, hs, rfl⟩
  have hc := tabJ_conj hsJ h
  rw [hsz'] at hc
  exact ⟨p.1, al, hal, Ev p.2, hsJ, hsz', _, _, _, _, _, _, rfl, hc⟩

theorem tab_alpha (hE : Mdl M Ev) (hJ : ∀ g, g ∈ J ↔ ∃ k < 256, Ev k = g)
    {RT : List (Nat × List Nat)} (hR : rtOK M RT = true) {z : Nat} {al : List Nat}
    (hz : z < 256) (hal : ∀ r ∈ al, r < 256)
    (hrec : ∀ x ∈ filterL (rootsOf RT 0) (aCand M z), ∃ q, aRec M z al x q = true)
    {α t g₁ g₂ h₁ h₂ : X} (h : TabJ J (Ev z) α t g₁ g₂ h₁ h₂) :
    ∃ r ∈ al, ∃ s ∈ J, s * Ev z * s⁻¹ = Ev z ∧ s * α * s⁻¹ = Ev r ∧
      ∃ t' g₁' g₂' h₁' h₂', TabJ J (Ev z) (Ev r) t' g₁' g₂' h₁' h₂' := by
  have h0 := h
  obtain ⟨⟨-, ha, -⟩, hζζ, hαα, htt, -, ht1, hαt, hc, hζt, hζα, -⟩ := h0
  obtain ⟨xa, hxa, rfl⟩ := (hJ _).1 ha
  have hone : (0 : Nat) < 256 := by norm_num
  have hrone : Ev 0 = 1 := hE.one
  have haz := mK_lt M xa z
  have hT2 := mK_lt M (mK M xa z) (mK M xa z)
  have hrT : Ev (mK M (mK M xa z) (mK M xa z)) = t := by
    rw [hE.mul haz haz, hE.mul hxa hz]
    exact tab_t hζζ hαα hζα
  have hsq : mK M xa xa = 0 :=
    hE.inj (mK_lt M _ _) hone (by rw [hE.mul hxa hxa, hαα, hrone])
  have hroot : xa ∈ rootsOf RT 0 := by
    have := rtOK_sound hR xa hxa
    rwa [hsq] at this
  have hcand : aCand M z xa = true := by
    unfold aCand
    simp only [letB_eq, andB_eq_true, notB_eq_true]
    refine ⟨beq_false fun h1 => ht1 (by rw [← hrT, h1, hrone]),
      beq_false fun h1 => hαt (by rw [← hrT, h1]),
      eqK hE (mK_lt M _ _) hone (by rw [hE.mul hT2 hT2, hrT, htt, hrone]),
      eqK hE (mK_lt M _ _) (mK_lt M _ _)
        (by rw [hE.mul hxa hT2, hE.mul hT2 hxa, hrT]; exact hc),
      eqK hE (mK_lt M _ _) (mK_lt M _ _)
        (by rw [hE.mul hz hT2, hE.mul hT2 hz, hrT]; exact hζt)⟩
  obtain ⟨q, hq⟩ := hrec xa (by rw [filterL_eq, List.mem_filter]; exact ⟨hroot, hcand⟩)
  unfold aRec at hq
  simp only [andB_eq_true, memN_eq_true, blt_eq_true, beq_eq_true] at hq
  obtain ⟨hr, hs, hsz, hsa⟩ := hq
  have hr2 := hal _ hr
  have hz' : Ev q.2 * Ev z * (Ev q.2)⁻¹ = Ev z := by
    have := congrArg Ev hsz
    rw [hE.mul hs hz, hE.mul hz hs] at this
    rw [this, mul_inv_cancel_right]
  have ha' : Ev q.2 * Ev xa * (Ev q.2)⁻¹ = Ev q.1 := by
    have := congrArg Ev hsa
    rw [hE.mul hs hxa, hE.mul hr2 hs] at this
    rw [this, mul_inv_cancel_right]
  have hsJ : Ev q.2 ∈ J := (hJ _).2 ⟨q.2, hs, rfl⟩
  have hc' := tabJ_conj hsJ h
  rw [hz', ha'] at hc'
  exact ⟨q.1, hr, Ev q.2, hsJ, hz', ha', _, _, _, _, _, hc'⟩

theorem search_sound (hE : Mdl M Ev) (hJ : ∀ g, g ∈ J ↔ ∃ k < 256, Ev k = g)
    {RT ZA : List (Nat × List Nat)} {ZC : List (Nat × Nat)} {AC : List (List (Nat × Nat))}
    {zc ac : Nat} (hR : rtOK M RT = true) (hZ : zOK M RT ZA ZC = true)
    (hA : zaGo M RT ZA AC = true) (hrows : rowsOK M RT zc ac ZA = true)
    {ζ α t g₁ g₂ h₁ h₂ : X} (h : TabJ J ζ α t g₁ g₂ h₁ h₂) :
    ∃ s ∈ J, s * ζ * s⁻¹ = Ev zc ∧ s * α * s⁻¹ = Ev ac ∧ zc < 256 ∧ ac < 256 := by
  obtain ⟨z, al, hzal, s1, hs1, hζ1, α', t', g₁', g₂', h₁', h₂', hα1, h1⟩ :=
    tab_zeta hE hJ hR hZ hA h
  obtain ⟨hz, hal, hrec⟩ := zaGo_sound hA (z, al) hzal
  obtain ⟨r, hr, s2, hs2, hζ2, hα2, t'', g₁'', g₂'', h₁'', h₂'', h2⟩ :=
    tab_alpha hE hJ hR hz hal hrec h1
  have hrow := rowsOK_sound hrows (z, al) hzal r hr
  by_cases hzr : z = zc ∧ r = ac
  · obtain ⟨e1, e2⟩ := hzr
    rw [← e1, ← e2]
    refine ⟨s2 * s1, J.mul_mem hs2 hs1, ?_, ?_, hz, hal r hr⟩
    · rw [mul_inv_rev]
      calc s2 * s1 * ζ * (s1⁻¹ * s2⁻¹) = s2 * (s1 * ζ * s1⁻¹) * s2⁻¹ := by group
        _ = Ev z := by rw [hζ1, hζ2]
    · rw [mul_inv_rev]
      calc s2 * s1 * α * (s1⁻¹ * s2⁻¹) = s2 * (s1 * α * s1⁻¹) * s2⁻¹ := by group
        _ = Ev r := by rw [hα1, hα2]
  · obtain ⟨⟨-, -, -, hG1, hG2, -⟩, hR''⟩ := h2
    exact (no_tab_row hE hJ hR hz (hal r hr) hrow hzr hG1 hG2 hR'').elim

end Search

theorem prep_unique {P : Nat} {g h : Equiv.Perm (Fin 820)} (hg : PRep 820 10 P g)
    (hh : PRep 820 10 P h) : g = h :=
  Equiv.ext fun x => Fin.ext ((hg x).symm.trans (hh x))

open Classical in
noncomputable def pv (P : Nat) : Equiv.Perm (Fin 820) :=
  if h : ∃ g, PRep 820 10 P g then h.choose else 1

theorem pv_eq {P : Nat} {g : Equiv.Perm (Fin 820)} (h : PRep 820 10 P g) : pv P = g := by
  have hex : ∃ g, PRep 820 10 P g := ⟨g, h⟩
  unfold pv
  rw [dif_pos hex]
  exact prep_unique hex.choose_spec h

noncomputable def evK (E : Nat → Nat) (a : Nat) : Equiv.Perm (Fin 820) := pv (E a)

theorem evK_eq {E : Nat → Nat} {a : Nat} {g : Equiv.Perm (Fin 820)} (h : PRep 820 10 (E a) g) :
    evK E a = g :=
  pv_eq h

theorem eq_of_prepK {P Q : Nat} {g : Equiv.Perm (Fin 820)} (hP : cK P = true) (hQ : cK Q = true)
    (gP : PRep 820 10 P g) (gQ : PRep 820 10 Q g) : P = Q := by
  obtain ⟨-, hw, hP1, -⟩ := CFSG.KS.PF.canon_facts hP
  obtain ⟨-, -, hQ1, -⟩ := CFSG.KS.PF.canon_facts hQ
  exact CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) hP1 hQ1 fun i hi => by
    rw [gP ⟨i, hi⟩, gQ ⟨i, hi⟩]

theorem inj_of_sortJ {cnt : Nat} {T S SI : Nat → Nat}
    (hS : ∀ i < cnt, S i < cnt ∧ SI (S i) = i ∧ (i + 1 < cnt → T (S i) < T (S (i + 1)))) :
    ∀ a < cnt, ∀ b < cnt, T a = T b → a = b := by
  have hmono : ∀ i j, i < j → j < cnt → T (S i) < T (S j) := by
    intro i j hij hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
      · exact lt_trans (ih h (by omega)) ((hS j (by omega)).2.2 hj)
      · subst h
        exact (hS i (by omega)).2.2 hj
  have hsurj : ∀ a < cnt, ∃ i < cnt, S i = a := by
    classical
    have himg : (Finset.range cnt).image S = Finset.range cnt := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
        exact Finset.mem_range.2 (hS i (Finset.mem_range.1 hi)).1
      · rw [Finset.card_image_of_injOn]
        intro i hi j hj e
        have h1 := (hS i (Finset.mem_range.1 hi)).2.1
        have h2 := (hS j (Finset.mem_range.1 hj)).2.1
        rw [← h1, ← h2]
        exact congrArg SI e
    intro a ha
    have : a ∈ (Finset.range cnt).image S := by rw [himg]; exact Finset.mem_range.2 ha
    obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
    exact ⟨i, Finset.mem_range.1 hi, e⟩
  intro a ha b hb e
  obtain ⟨i, hi, rfl⟩ := hsurj a ha
  obtain ⟨j, hj, rfl⟩ := hsurj b hb
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd e (Nat.ne_of_lt (hmono i j h hj))
  · rw [h]
  · exact absurd e.symm (Nat.ne_of_lt (hmono j i h hi))

section Facts

variable {L E G M : Nat → Nat} {RP PA LA SO SI IV : Nat}

theorem tree_facts (h : treeOK E RP PA LA = true) : E 0 = pidK ∧ ∀ i, 0 < i → i < 256 →
    f8 PA i < i ∧ f8 LA i < 3 ∧ f8 RP (3 * f8 PA i + f8 LA i) = i := by
  unfold treeOK at h
  rw [andB_eq_true, allN_eq_true] at h
  refine ⟨beq_eq_true.1 h.1, fun i hi0 hi => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h2 := h.2 j (by omega)
  simp only [letB_eq, andB_eq_true, blt_eq_true, beq_eq_true] at h2
  exact h2

theorem rec_facts (hrec : ∀ s < 16, recR E G RP (16 * s) 16 = true) :
    ∀ i < 256, ∀ k < 3, f8 RP (3 * i + k) < 256 ∧ E (f8 RP (3 * i + k)) = pc (E i) (G k) := by
  intro i hi k hk
  obtain ⟨s, j, hs, hj, rfl⟩ : ∃ s j, s < 16 ∧ j < 16 ∧ i = 16 * s + j :=
    ⟨i / 16, i % 16, by omega, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod i 16).symm⟩
  have h := allN_eq_true.1 (hrec s hs) j hj
  simp only [letB_eq] at h
  have h3 := allN_eq_true.1 h k hk
  simp only [letB_eq, andB_eq_true, blt_eq_true, beq_eq_true] at h3
  exact h3

theorem mt_facts (hmt : ∀ s < 8, mtR M RP PA LA (32 * s) 32 = true) : ∀ a < 256,
    mK M a 0 = a ∧ ∀ b, 0 < b → b < 256 → mK M a b = f8 RP (3 * mK M a (f8 PA b) + f8 LA b) := by
  intro a ha
  obtain ⟨s, j, hs, hj, rfl⟩ : ∃ s j, s < 8 ∧ j < 32 ∧ a = 32 * s + j :=
    ⟨a / 32, a % 32, by omega, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod a 32).symm⟩
  have h := allN_eq_true.1 (hmt s hs) j hj
  simp only [letB_eq] at h
  unfold rowM at h
  rw [andB_eq_true, allN_eq_true] at h
  refine ⟨beq_eq_true.1 h.1, fun b hb0 hb => ?_⟩
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  have h2 := h.2 c (by omega)
  simp only [letB_eq, beq_eq_true] at h2
  exact h2

theorem iv_facts (hiv : ivOK M IV = true) : ∀ a < 256, mK M a (f8 IV a) = 0 := by
  intro a ha
  have h := allN_eq_true.1 hiv a ha
  simp only [letB_eq, andB_eq_true, beq_eq_true] at h
  exact h.2

theorem sort_facts (hsort : sortOK E SO SI = true) :
    (∀ a < 256, cK (E a) = true ∧ f8 SO a < 256 ∧ f8 SI (f8 SO a) = a) ∧
      ∀ j < 255, E (f8 SO j) < E (f8 SO (j + 1)) := by
  unfold sortOK at hsort
  rw [andB_eq_true, allN_eq_true, allN_eq_true] at hsort
  refine ⟨fun a ha => ?_, fun j hj => blt_eq_true.1 (hsort.2 j hj)⟩
  have h := hsort.1 a ha
  simp only [andB_eq_true, blt_eq_true, beq_eq_true] at h
  exact h

theorem genGo_sound : ∀ (GW : List (List Nat)) (k0 : Nat),
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun w _ ih k => andB (Nat.beq (G k) (wordK L w)) (ih (Nat.succ k))) GW k0 = true →
      ∀ i < GW.length, ∃ w, G (k0 + i) = wordK L w
  | [], _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | w :: GW, k0, h, i, hi => by
    change andB (Nat.beq (G k0) (wordK L w)) _ = true at h
    rw [andB_eq_true] at h
    cases i with
    | zero => exact ⟨w, beq_eq_true.1 h.1⟩
    | succ i =>
      obtain ⟨v, hv⟩ := genGo_sound GW (k0 + 1) h.2 i (by simpa using hi)
      refine ⟨v, ?_⟩
      rw [← hv]
      congr 1
      omega

theorem wordK_prep {H : Subgroup (Equiv.Perm (Fin 820))}
    (hL : ∀ l, ∃ g ∈ H, PRep 820 10 (L l) g) :
    ∀ w : List Nat, ∃ g ∈ H, PRep 820 10 (wordK L w) g
  | [] => ⟨1, H.one_mem, prep_pidn (by norm_num) (by norm_num)⟩
  | l :: w => by
    obtain ⟨g, hg, hP⟩ := hL l
    obtain ⟨h, hh, hQ⟩ := wordK_prep hL w
    exact ⟨g * h, H.mul_mem hg hh, prep_pcomp (by norm_num) hP hQ⟩

end Facts

section Sub

variable {X : Type*} [Group X] {M : Nat → Nat}

def jSub (Ev : Nat → X) (hmul : ∀ a < 256, ∀ b < 256, Ev (mK M a b) = Ev a * Ev b)
    (hone : Ev 0 = 1) (hinv : ∀ a < 256, ∃ b < 256, Ev b = (Ev a)⁻¹) : Subgroup X where
  carrier := {g | ∃ a, a < 256 ∧ Ev a = g}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨mK M a b, mK_lt M a b, hmul a ha b hb⟩
  one_mem' := ⟨0, by norm_num, hone⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact hinv a ha

theorem card_jSub {Ev : Nat → X} {hmul : ∀ a < 256, ∀ b < 256, Ev (mK M a b) = Ev a * Ev b}
    {hone : Ev 0 = 1} {hinv : ∀ a < 256, ∃ b < 256, Ev b = (Ev a)⁻¹}
    (hinj : ∀ a < 256, ∀ b < 256, Ev a = Ev b → a = b) :
    Nat.card (jSub Ev hmul hone hinv) = 256 := by
  have hbij : Function.Bijective (fun a : Fin 256 =>
      (⟨Ev a, ⟨a, a.2, rfl⟩⟩ : (jSub Ev hmul hone hinv : Subgroup X))) := by
    constructor
    · intro a b hab
      exact Fin.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab))
    · intro x
      obtain ⟨a, ha, hg⟩ := x.2
      exact ⟨⟨a, ha⟩, Subtype.ext hg⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_fin]

end Sub

theorem cert_of_checks {L E G M : Nat → Nat} {RP PA LA SO SI IV : Nat}
    {RT ZA : List (Nat × List Nat)} {ZC : List (Nat × Nat)} {AC : List (List (Nat × Nat))}
    {GW : List (List Nat)} {CW : List Nat} {zc ac : Nat} {H : Subgroup (Equiv.Perm (Fin 820))}
    (hL : ∀ l, ∃ g ∈ H, PRep 820 10 (L l) g) (hgen : genOK L G GW = true)
    (hgw : 3 ≤ GW.length) (hcw : cwOK L E CW zc ac = true) (htree : treeOK E RP PA LA = true)
    (hrec : ∀ s < 16, recR E G RP (16 * s) 16 = true)
    (hmt : ∀ s < 8, mtR M RP PA LA (32 * s) 32 = true) (hiv : ivOK M IV = true)
    (hsort : sortOK E SO SI = true) (hrt : rtOK M RT = true) (hz : zOK M RT ZA ZC = true)
    (hza : zaGo M RT ZA AC = true) (hrows : rowsOK M RT zc ac ZA = true) :
    ∃ J : Subgroup (Equiv.Perm (Fin 820)), J ≤ H ∧ Nat.card J = 256 ∧
      ∀ ζ ∈ J, ∀ α ∈ J, ∀ t ∈ J, ∀ g₁ ∈ J, ∀ g₂ ∈ J, ∀ h₁ ∈ J, ∀ h₂ ∈ J,
        OuterTable ζ α t g₁ g₂ h₁ h₂ → ∃ k ∈ H, k * ζ * k⁻¹ = α := by
  have hn32 : 820 < 2 ^ 32 := by norm_num
  have hid : PRep 820 10 pidK 1 := prep_pidn (by norm_num) (by norm_num)
  obtain ⟨hE0, htr⟩ := tree_facts htree
  have hrc := rec_facts hrec
  have hmf := mt_facts hmt
  have hG : ∀ k < 3, ∃ g ∈ H, PRep 820 10 (G k) g := by
    intro k hk
    obtain ⟨w, hw⟩ := genGo_sound GW 0 hgen k (by omega)
    rw [Nat.zero_add] at hw
    rw [hw]
    exact wordK_prep hL w
  have hGv : ∀ k < 3, PRep 820 10 (G k) (pv (G k)) := fun k hk => by
    obtain ⟨g, -, hP⟩ := hG k hk
    rw [pv_eq hP]
    exact hP
  have hEl : ∀ i < 256, ∃ g ∈ H, PRep 820 10 (E i) g := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · exact ⟨1, H.one_mem, by rw [hE0]; exact hid⟩
      · obtain ⟨hp, hl, hr⟩ := htr i hpos hi
        obtain ⟨g, hg, hPg⟩ := ih _ hp (by omega)
        obtain ⟨x, hx, hPx⟩ := hG _ hl
        have e := (hrc (f8 PA i) (by omega) (f8 LA i) hl).2
        rw [hr] at e
        exact ⟨g * x, H.mul_mem hg hx, by rw [e]; exact prep_pcomp hn32 hPg hPx⟩
  have hPE : ∀ a < 256, PRep 820 10 (E a) (evK E a) ∧ evK E a ∈ H := by
    intro a ha
    obtain ⟨g, hg, hP⟩ := hEl a ha
    rw [evK_eq hP]
    exact ⟨hP, hg⟩
  have hone : evK E 0 = 1 := evK_eq (by rw [hE0]; exact hid)
  have hmul : ∀ b < 256, ∀ a < 256, evK E (mK M a b) = evK E a * evK E b := by
    intro b
    induction b using Nat.strong_induction_on with
    | _ b ih =>
      intro hb a ha
      rcases Nat.eq_zero_or_pos b with rfl | hpos
      · rw [hone, mul_one, (hmf a ha).1]
      · obtain ⟨hp, hl, hr⟩ := htr b hpos hb
        have ih' := ih _ hp (by omega) a ha
        have e1 := (hrc _ (mK_lt M a (f8 PA b)) _ hl).2
        have e2 := (hmf a ha).2 b hpos hb
        have e3 := (hrc _ (by omega : f8 PA b < 256) _ hl).2
        rw [hr] at e3
        have hb' : evK E b = evK E (f8 PA b) * pv (G (f8 LA b)) :=
          evK_eq (by rw [e3]; exact prep_pcomp hn32 (hPE _ (by omega)).1 (hGv _ hl))
        have hab : PRep 820 10 (E (mK M a b)) (evK E (mK M a (f8 PA b)) * pv (G (f8 LA b))) := by
          rw [e2, e1]
          exact prep_pcomp hn32 (hPE _ (mK_lt M _ _)).1 (hGv _ hl)
        rw [evK_eq hab, ih', hb', mul_assoc]
  obtain ⟨hsf1, hsf2⟩ := sort_facts hsort
  have hEinj : ∀ a < 256, ∀ b < 256, E a = E b → a = b :=
    inj_of_sortJ (S := f8 SO) (SI := f8 SI) fun i hi =>
      ⟨(hsf1 i hi).2.1, (hsf1 i hi).2.2, fun h => hsf2 i (by omega)⟩
  have hinj : ∀ a < 256, ∀ b < 256, evK E a = evK E b → a = b := by
    intro a ha b hb h
    apply hEinj a ha b hb
    exact eq_of_prepK (hsf1 a ha).1 (hsf1 b hb).1 (hPE a ha).1 (by rw [h]; exact (hPE b hb).1)
  have hinv : ∀ a < 256, ∃ b < 256, evK E b = (evK E a)⁻¹ := fun a ha =>
    ⟨f8 IV a, f8_lt _ _, eq_inv_of_mul_eq_one_right (by
      rw [← hmul _ (f8_lt _ _) a ha, iv_facts hiv a ha, hone])⟩
  have hmul' : ∀ a < 256, ∀ b < 256, evK E (mK M a b) = evK E a * evK E b :=
    fun a ha b hb => hmul b hb a ha
  have hMdl : Mdl M (evK E) := ⟨fun hx hy => hmul _ hy _ hx, fun hx hy h => hinj _ hx _ hy h, hone⟩
  have hJH : jSub (evK E) hmul' hone hinv ≤ H := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hPE a ha).2
  refine ⟨jSub (evK E) hmul' hone hinv, hJH, card_jSub hinj, ?_⟩
  intro ζ hζ α hα t ht g₁ hg₁ g₂ hg₂ h₁ hh₁ h₂ hh₂ hT
  obtain ⟨s, hs, hsζ, hsα, hzc, hac⟩ := search_sound hMdl
    (J := jSub (evK E) hmul' hone hinv) (fun g => Iff.rfl) hrt hz hza hrows
    (⟨⟨hζ, hα, ht, hg₁, hg₂, hh₁, hh₂⟩, tabR_of_outerTable hT⟩ :
      TabJ (jSub (evK E) hmul' hone hinv) ζ α t g₁ g₂ h₁ h₂)
  obtain ⟨W, hW, hPW⟩ := wordK_prep hL CW
  unfold cwOK at hcw
  simp only [letB_eq, beq_eq_true] at hcw
  have h1 : PRep 820 10 (pc (wordK L CW) (E zc)) (W * evK E zc) :=
    prep_pcomp hn32 hPW (hPE zc hzc).1
  have h2 : PRep 820 10 (pc (wordK L CW) (E zc)) (evK E ac * W) := by
    rw [hcw]
    exact prep_pcomp hn32 (hPE ac hac).1 hPW
  have hWc : W * evK E zc * W⁻¹ = evK E ac := mul_inv_eq_iff_eq_mul.2 (prep_unique h1 h2)
  have hsH := hJH hs
  refine ⟨s⁻¹ * W * s, H.mul_mem (H.mul_mem (H.inv_mem hsH) hW) hsH, ?_⟩
  have hζ' : ζ = s⁻¹ * evK E zc * s := by
    rw [← hsζ]
    group
  have hα' : α = s⁻¹ * evK E ac * s := by
    rw [← hsα]
    group
  rw [hζ', hα', ← hWc]
  group

end CFSG.KC.TS8JKSound
