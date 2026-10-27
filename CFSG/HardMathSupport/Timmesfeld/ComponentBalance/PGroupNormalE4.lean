module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Torsion
public import CFSG.RankThree.PGroups.MaximalNormalElementaryCentralizer
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointRankFour
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.RankFourTheoremC.Refined
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
public import CFSG.LocalAnalysis.SectionRank.Ccomm.OddCritical
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

section LemmaM


def e4m_N {A : Type*} [AddCommGroup A] (β : A →+ A) : A →+ A := β - AddMonoidHom.id A

lemma e4m_N_apply {A : Type*} [AddCommGroup A] (β : A →+ A) (a : A) :
    e4m_N β a = β a - a := by simp [e4m_N]

lemma e4m_rel {A : Type*} [AddCommGroup A] (β : A →+ A) (h : ∀ a, β (β (β a)) = a) (a : A) :
    e4m_N β (e4m_N β (e4m_N β a)) + 3 • e4m_N β (e4m_N β a) + 3 • e4m_N β a = 0 := by
  simp only [e4m_N_apply, map_sub, h]
  abel

lemma e4m_Ny_eq {A : Type*} [AddCommGroup A] (β₁ β₂ : A →+ A) (x : A) :
    e4m_N (β₁.comp β₂) x = e4m_N β₁ x + e4m_N β₂ x + e4m_N β₁ (e4m_N β₂ x) := by
  simp only [e4m_N_apply, map_sub, AddMonoidHom.comp_apply]
  abel

lemma e4m_Ny'_eq {A : Type*} [AddCommGroup A] (β₁ β₂ : A →+ A) (x : A) :
    e4m_N (β₁.comp (β₂.comp β₂)) x = e4m_N β₁ x + 2 • e4m_N β₂ x + e4m_N β₂ (e4m_N β₂ x)
      + 2 • e4m_N β₁ (e4m_N β₂ x) + e4m_N β₁ (e4m_N β₂ (e4m_N β₂ x)) := by
  simp only [e4m_N_apply, map_sub, AddMonoidHom.comp_apply]
  abel

def e4m_R {A : Type*} [AddCommGroup A] (U : AddSubgroup A) (e : A) (x : A) (t : ℕ) : Prop :=
  x - t • e ∈ U

structure E4mGood {A : Type*} [AddCommGroup A] (U : AddSubgroup A) (e : A) (n : A →+ A) :
    Prop where
  rel : ∀ a, n (n (n a)) + 3 • n (n a) + 3 • n a = 0
  mem : n e ∈ U
  kill : ∀ u ∈ U, n u = 0
  inj : ∀ k : ℕ, k • n e = 0 → 3 ∣ k

structure E4mCtx {A : Type*} [AddCommGroup A] (β₁ β₂ : A →+ A) (U : AddSubgroup A) (e : A) :
    Prop where
  hcomm : ∀ a, β₁ (β₂ a) = β₂ (β₁ a)
  h₁ : ∀ a, β₁ (β₁ (β₁ a)) = a
  h₂ : ∀ a, β₂ (β₂ (β₂ a)) = a
  hU3 : ∀ u ∈ U, 3 • u = 0
  hU₁ : ∀ u ∈ U, β₁ u = u
  hU₂ : ∀ u ∈ U, β₂ u = u
  he3 : 3 • e = 0
  hE : ∀ a : A, 3 • a = 0 → ∃ u ∈ U, ∃ s : ℕ, a = u + s • e
  hNe₁ : β₁ e - e ∈ U
  hNe₂ : β₂ e - e ∈ U
  hind : ∀ s t : ℕ, s • (β₁ e - e) + t • (β₂ e - e) = 0 → 3 ∣ s ∧ 3 ∣ t

section generic

variable {A : Type*} [AddCommGroup A] {U : AddSubgroup A} {e : A}

lemma e4m_R_add {x y : A} {s t : ℕ} (hx : e4m_R U e x s) (hy : e4m_R U e y t) :
    e4m_R U e (x + y) (s + t) := by
  unfold e4m_R at *
  have : x + y - (s + t) • e = (x - s • e) + (y - t • e) := by rw [add_nsmul]; abel
  rw [this]; exact U.add_mem hx hy

lemma e4m_R_nsmul (k : ℕ) {x : A} {s : ℕ} (hx : e4m_R U e x s) :
    e4m_R U e (k • x) (k * s) := by
  unfold e4m_R at *
  have : k • x - (k * s) • e = k • (x - s • e) := by rw [smul_sub, smul_smul]
  rw [this]; exact U.nsmul_mem hx k

lemma e4m_R_congr {x y : A} {s : ℕ} (hx : e4m_R U e x s) (h : y - x ∈ U) :
    e4m_R U e y s := by
  unfold e4m_R at *
  have : y - s • e = (y - x) + (x - s • e) := by abel
  rw [this]; exact U.add_mem h hx

lemma e4m_R_of_mem {u : A} (h : u ∈ U) : e4m_R U e u 0 := by
  unfold e4m_R; simpa using h

lemma e4m_smul3 (m : ℕ) (x : A) (h : 3 • x = 0) : (3 * m) • x = 0 := by
  rw [mul_comm, ← smul_smul, h, smul_zero]

lemma e4m_E_add {x y : A} (h1 : 3 • x = 0) (h2 : 3 • y = 0) : 3 • (x + y) = 0 := by
  rw [smul_add, h1, h2, add_zero]

lemma e4m_E_nsmul (k : ℕ) {x : A} (h : 3 • x = 0) : 3 • (k • x) = 0 := by
  rw [smul_comm, h, smul_zero]

lemma e4m_apply_R {n : A →+ A} (hn : ∀ u ∈ U, n u = 0) {z : A} {s : ℕ}
    (h : e4m_R U e z s) : n z = s • n e := by
  have : z = (z - s • e) + s • e := by abel
  rw [this, map_add, map_nsmul, hn _ h, zero_add]

lemma e4m_three_apply {n : A →+ A} (hn : ∀ u ∈ U, n u = 0) {a : A} {s : ℕ}
    (h : e4m_R U e (3 • a) s) : 3 • n a = s • n e := by
  rw [← map_nsmul]; exact e4m_apply_R hn h

lemma e4m_E_of_lvl2 {n : A →+ A} (hn : E4mGood U e n) {x : A} (hx : 3 • x ∈ U) :
    3 • n x = 0 := by
  rw [← map_nsmul]; exact hn.kill _ hx

end generic

namespace E4mCtx

variable {A : Type*} [AddCommGroup A] {β₁ β₂ : A →+ A} {U : AddSubgroup A} {e : A}
  (C : E4mCtx β₁ β₂ U e)
include C

lemma R_of_E {z : A} (hz : 3 • z = 0) : ∃ s, e4m_R U e z s := by
  obtain ⟨u, hu, s, hs⟩ := C.hE z hz
  refine ⟨s, ?_⟩
  unfold e4m_R; rw [hs]; simpa using hu

lemma N_comm (x : A) : e4m_N β₁ (e4m_N β₂ x) = e4m_N β₂ (e4m_N β₁ x) := by
  simp only [e4m_N_apply, map_sub, C.hcomm]; abel

lemma kE {k : ℕ} (hk : k • e ∈ U) : 3 ∣ k := by
  have h0 : β₁ (k • e) - k • e = 0 := by rw [C.hU₁ _ hk]; exact sub_self _
  rw [map_nsmul, ← smul_sub] at h0
  exact (C.hind k 0 (by simpa using h0)).1

lemma R_unique {z : A} {s t : ℕ} (hs : e4m_R U e z s) (ht : e4m_R U e z t) :
    s % 3 = t % 3 := by
  rcases le_total s t with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have hk : k • e ∈ U := by
      have e1 : k • e = (z - s • e) - (z - (s + k) • e) := by rw [add_nsmul]; abel
      rw [e1]; exact U.sub_mem hs ht
    have := C.kE hk; omega
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    have hk : k • e ∈ U := by
      have e1 : k • e = (z - t • e) - (z - (t + k) • e) := by rw [add_nsmul]; abel
      rw [e1]; exact U.sub_mem ht hs
    have := C.kE hk; omega

lemma good₁ : E4mGood U e (e4m_N β₁) where
  rel := e4m_rel β₁ C.h₁
  mem := by rw [e4m_N_apply]; exact C.hNe₁
  kill := fun u hu => by rw [e4m_N_apply, C.hU₁ u hu, sub_self]
  inj := fun k hk => by
    rw [e4m_N_apply] at hk
    exact (C.hind k 0 (by simpa using hk)).1

lemma good₂ : E4mGood U e (e4m_N β₂) where
  rel := e4m_rel β₂ C.h₂
  mem := by rw [e4m_N_apply]; exact C.hNe₂
  kill := fun u hu => by rw [e4m_N_apply, C.hU₂ u hu, sub_self]
  inj := fun k hk => by
    rw [e4m_N_apply] at hk
    exact (C.hind 0 k (by simpa using hk)).2

lemma Ny_e : e4m_N (β₁.comp β₂) e = e4m_N β₁ e + e4m_N β₂ e := by
  rw [e4m_Ny_eq, C.good₁.kill _ C.good₂.mem, add_zero]

lemma Ny'_e : e4m_N (β₁.comp (β₂.comp β₂)) e = e4m_N β₁ e + 2 • e4m_N β₂ e := by
  rw [e4m_Ny'_eq, C.good₂.kill _ C.good₂.mem, C.good₁.kill _ C.good₂.mem]
  simp

lemma goodY : E4mGood U e (e4m_N (β₁.comp β₂)) where
  rel := e4m_rel _ (fun a => by simp only [AddMonoidHom.comp_apply, C.hcomm, C.h₁, C.h₂])
  mem := by rw [C.Ny_e]; exact U.add_mem C.good₁.mem C.good₂.mem
  kill := fun u hu => by
    rw [e4m_Ny_eq, C.good₁.kill _ hu, C.good₂.kill _ hu, map_zero]; simp
  inj := fun k hk => by
    rw [C.Ny_e, smul_add] at hk
    simp only [e4m_N_apply] at hk
    exact (C.hind k k hk).1

lemma goodY' : E4mGood U e (e4m_N (β₁.comp (β₂.comp β₂))) where
  rel := e4m_rel _ (fun a => by simp only [AddMonoidHom.comp_apply, C.hcomm, C.h₁, C.h₂])
  mem := by
    rw [C.Ny'_e]
    exact U.add_mem C.good₁.mem (U.nsmul_mem C.good₂.mem 2)
  kill := fun u hu => by
    rw [e4m_Ny'_eq, C.good₁.kill _ hu, C.good₂.kill _ hu]
    simp
  inj := fun k hk => by
    rw [C.Ny'_e, smul_add] at hk
    have h2 : ∀ x : A, k • (2 • x) = (2 * k) • x := fun x => by rw [smul_smul, mul_comm]
    rw [h2] at hk
    simp only [e4m_N_apply] at hk
    exact (C.hind k (2 * k) hk).1

lemma good_mem_of_E {n : A →+ A} (hn : E4mGood U e n) {z : A} (hz : 3 • z = 0) : n z ∈ U := by
  obtain ⟨s, hs⟩ := C.R_of_E hz
  rw [e4m_apply_R hn.kill hs]; exact U.nsmul_mem hn.mem s

lemma lvl2_Ny {x : A} (hx : 3 • x ∈ U) :
    e4m_N (β₁.comp β₂) x - (e4m_N β₁ x + e4m_N β₂ x) ∈ U := by
  have hE2 : 3 • e4m_N β₂ x = 0 := e4m_E_of_lvl2 C.good₂ hx
  rw [e4m_Ny_eq, add_sub_cancel_left]
  exact C.good_mem_of_E C.good₁ hE2

lemma lvl2_Ny' {x : A} (hx : 3 • x ∈ U) :
    e4m_N (β₁.comp (β₂.comp β₂)) x - (e4m_N β₁ x + 2 • e4m_N β₂ x) ∈ U := by
  have hE2 : 3 • e4m_N β₂ x = 0 := e4m_E_of_lvl2 C.good₂ hx
  have h22 : e4m_N β₂ (e4m_N β₂ x) ∈ U := C.good_mem_of_E C.good₂ hE2
  have h12 : e4m_N β₁ (e4m_N β₂ x) ∈ U := C.good_mem_of_E C.good₁ hE2
  have h122 : e4m_N β₁ (e4m_N β₂ (e4m_N β₂ x)) ∈ U := by
    rw [C.good₁.kill _ h22]; exact U.zero_mem
  have : e4m_N (β₁.comp (β₂.comp β₂)) x - (e4m_N β₁ x + 2 • e4m_N β₂ x)
      = e4m_N β₂ (e4m_N β₂ x) + 2 • e4m_N β₁ (e4m_N β₂ x)
        + e4m_N β₁ (e4m_N β₂ (e4m_N β₂ x)) := by
    rw [e4m_Ny'_eq]; abel
  rw [this]
  exact U.add_mem (U.add_mem h22 (U.nsmul_mem h12 2)) h122

lemma CT {d₁ d₂ : A} (h1 : 3 • d₁ = 0) (h2 : 3 • d₂ = 0)
    (h : e4m_N β₁ d₂ = e4m_N β₂ d₁) : d₁ ∈ U ∧ d₂ ∈ U := by
  obtain ⟨v₁, hv₁, s₁, hs₁⟩ := C.hE d₁ h1
  obtain ⟨v₂, hv₂, s₂, hs₂⟩ := C.hE d₂ h2
  have R1 : e4m_R U e d₁ s₁ := by unfold e4m_R; rw [hs₁]; simpa using hv₁
  have R2 : e4m_R U e d₂ s₂ := by unfold e4m_R; rw [hs₂]; simpa using hv₂
  rw [e4m_apply_R C.good₁.kill R2, e4m_apply_R C.good₂.kill R1] at h
  simp only [e4m_N_apply] at h
  have h3 : 3 • (β₂ e - e) = 0 := C.hU3 _ C.hNe₂
  have h' : s₂ • (β₁ e - e) + (2 * s₁) • (β₂ e - e) = 0 := by
    rw [h, ← add_nsmul]
    have : s₁ + 2 * s₁ = 3 * s₁ := by ring
    rw [this]; exact e4m_smul3 s₁ _ h3
  obtain ⟨h31, h32⟩ := C.hind _ _ h'
  have h31' : 3 ∣ s₁ := by omega
  obtain ⟨m₁, hm₁⟩ := h31'
  obtain ⟨m₂, hm₂⟩ := h31
  refine ⟨?_, ?_⟩
  · rw [hs₁, hm₁, e4m_smul3 m₁ _ C.he3, add_zero]; exact hv₁
  · rw [hs₂, hm₂, e4m_smul3 m₂ _ C.he3, add_zero]; exact hv₂

lemma key {n : A →+ A} (hn : E4mGood U e n) {a : A} {s : ℕ}
    (hs : e4m_R U e (3 • a) s) : ∃ t, e4m_R U e (n (n a)) t ∧ 3 ∣ t + s := by
  have h3 : 3 • n a = s • n e := e4m_three_apply hn.kill hs
  have h3' : 3 • n (n a) = 0 := by
    rw [← map_nsmul, h3, map_nsmul, hn.kill _ hn.mem, smul_zero]
  obtain ⟨t, hR⟩ := C.R_of_E h3'
  refine ⟨t, hR, ?_⟩
  have h1 := hn.rel a
  rw [e4m_apply_R hn.kill hR, h3', h3, add_zero] at h1
  rw [← add_nsmul] at h1
  exact hn.inj _ h1

lemma P2 {a : A} (ha : 3 • (3 • a) = 0) : e4m_N β₁ a ∈ U ∧ e4m_N β₂ a ∈ U := by
  obtain ⟨s, hR⟩ := C.R_of_E ha
  have g₁ := C.good₁
  have g₂ := C.good₂
  have hd₁ : 3 • e4m_N β₁ a = s • e4m_N β₁ e := e4m_three_apply g₁.kill hR
  have hd₂ : 3 • e4m_N β₂ a = s • e4m_N β₂ e := e4m_three_apply g₂.kill hR
  have l₁ : 3 • e4m_N β₁ a ∈ U := by rw [hd₁]; exact U.nsmul_mem g₁.mem s
  have l₂ : 3 • e4m_N β₂ a ∈ U := by rw [hd₂]; exact U.nsmul_mem g₂.mem s
  by_cases h3 : 3 ∣ s
  · obtain ⟨m, rfl⟩ := h3
    have z₁ : 3 • e4m_N β₁ a = 0 := by
      rw [hd₁]; exact e4m_smul3 m _ (C.hU3 _ g₁.mem)
    have z₂ : 3 • e4m_N β₂ a = 0 := by
      rw [hd₂]; exact e4m_smul3 m _ (C.hU3 _ g₂.mem)
    exact C.CT z₁ z₂ (C.N_comm a)
  · exfalso
    obtain ⟨t11, r11, c11⟩ := C.key g₁ hR
    obtain ⟨t22, r22, c22⟩ := C.key g₂ hR
    obtain ⟨ty, ry, cy⟩ := C.key C.goodY hR
    obtain ⟨ty', ry', cy'⟩ := C.key C.goodY' hR
    have e12 : 3 • e4m_N β₁ (e4m_N β₂ a) = 0 := e4m_E_of_lvl2 g₁ l₂
    have e22 : 3 • e4m_N β₂ (e4m_N β₂ a) = 0 := e4m_E_of_lvl2 g₂ l₂
    obtain ⟨t12, r12⟩ := C.R_of_E e12
    have r21 : e4m_R U e (e4m_N β₂ (e4m_N β₁ a)) t12 := by
      rw [← C.N_comm]; exact r12
    have hNy : e4m_R U e (e4m_N (β₁.comp β₂) (e4m_N (β₁.comp β₂) a))
        (t11 + t12 + (t12 + t22) + 0) := by
      rw [e4m_Ny_eq β₁ β₂ a, map_add, map_add]
      refine e4m_R_add (e4m_R_add ?_ ?_) ?_
      · exact e4m_R_congr (e4m_R_add r11 r21) (C.lvl2_Ny l₁)
      · exact e4m_R_congr (e4m_R_add r12 r22) (C.lvl2_Ny l₂)
      · exact e4m_R_of_mem (C.good_mem_of_E C.goodY e12)
    have hz : 3 • (e4m_N β₂ (e4m_N β₂ a) + 2 • e4m_N β₁ (e4m_N β₂ a)
        + e4m_N β₁ (e4m_N β₂ (e4m_N β₂ a))) = 0 := by
      refine e4m_E_add (e4m_E_add e22 (e4m_E_nsmul 2 e12)) ?_
      exact e4m_E_of_lvl2 g₁ (by rw [e22]; exact U.zero_mem)
    have hNy' : e4m_R U e (e4m_N (β₁.comp (β₂.comp β₂)) (e4m_N (β₁.comp (β₂.comp β₂)) a))
        (t11 + 2 * t12 + 2 * (t12 + 2 * t22) + 0) := by
      have eq1 : e4m_N (β₁.comp (β₂.comp β₂)) a
          = (e4m_N β₁ a + 2 • e4m_N β₂ a) + (e4m_N β₂ (e4m_N β₂ a)
            + 2 • e4m_N β₁ (e4m_N β₂ a) + e4m_N β₁ (e4m_N β₂ (e4m_N β₂ a))) := by
        rw [e4m_Ny'_eq]; abel
      rw [eq1, map_add, map_add, map_nsmul]
      refine e4m_R_add (e4m_R_add ?_ ?_) ?_
      · exact e4m_R_congr (e4m_R_add r11 (e4m_R_nsmul 2 r21)) (C.lvl2_Ny' l₁)
      · exact e4m_R_nsmul 2 (e4m_R_congr (e4m_R_add r12 (e4m_R_nsmul 2 r22)) (C.lvl2_Ny' l₂))
      · exact e4m_R_of_mem (C.good_mem_of_E C.goodY' hz)
    have u1 := C.R_unique ry hNy
    have u2 := C.R_unique ry' hNy'
    omega

lemma Q (k : ℕ) : ∀ a : A, 3 ^ (k + 2) • a = 0 → e4m_N β₁ a ∈ U ∧ e4m_N β₂ a ∈ U := by
  induction k with
  | zero =>
    intro a ha
    apply C.P2
    rw [smul_smul]; simpa using ha
  | succ k ih =>
    intro a ha
    have h1 : 3 ^ (k + 2) • (3 • a) = 0 := by
      rw [smul_smul, ← pow_succ]; exact ha
    obtain ⟨q₁, q₂⟩ := ih (3 • a) h1
    rw [map_nsmul] at q₁ q₂
    have g₁ := C.good₁
    have g₂ := C.good₂
    have p1 := C.P2 (a := e4m_N β₁ a) (by rw [C.hU3 _ q₁])
    have p2 := C.P2 (a := e4m_N β₂ a) (by rw [C.hU3 _ q₂])
    have z₁ : 3 • e4m_N β₁ a = 0 := by
      have := g₁.rel a
      rw [g₁.kill _ p1.1, C.hU3 _ p1.1, zero_add, zero_add] at this
      exact this
    have z₂ : 3 • e4m_N β₂ a = 0 := by
      have := g₂.rel a
      rw [g₂.kill _ p2.2, C.hU3 _ p2.2, zero_add, zero_add] at this
      exact this
    exact C.CT z₁ z₂ (C.N_comm a)

end E4mCtx

theorem e4_lemmaM {A : Type*} [AddCommGroup A]
    (hA : ∀ a : A, ∃ k : ℕ, 3 ^ k • a = 0)
    (β₁ β₂ : A →+ A) (hcomm : ∀ a, β₁ (β₂ a) = β₂ (β₁ a))
    (hβ₁ : ∀ a, β₁ (β₁ (β₁ a)) = a) (hβ₂ : ∀ a, β₂ (β₂ (β₂ a)) = a)
    (U : AddSubgroup A) (e : A)
    (hU3 : ∀ u ∈ U, 3 • u = 0) (hU₁ : ∀ u ∈ U, β₁ u = u) (hU₂ : ∀ u ∈ U, β₂ u = u)
    (he3 : 3 • e = 0)
    (hE : ∀ a : A, 3 • a = 0 → ∃ u ∈ U, ∃ s : ℕ, a = u + s • e)
    (hNe₁ : β₁ e - e ∈ U) (hNe₂ : β₂ e - e ∈ U)
    (hind : ∀ s t : ℕ, s • (β₁ e - e) + t • (β₂ e - e) = 0 → 3 ∣ s ∧ 3 ∣ t) :
    ∀ a : A, β₁ a - a ∈ U ∧ β₂ a - a ∈ U := by
  have C : E4mCtx β₁ β₂ U e :=
    ⟨hcomm, hβ₁, hβ₂, hU3, hU₁, hU₂, he3, hE, hNe₁, hNe₂, hind⟩
  intro a
  obtain ⟨k, hk⟩ := hA a
  have h : 3 ^ (k + 2) • a = 0 := by
    rw [pow_add, mul_comm, ← smul_smul, hk, smul_zero]
  have := C.Q k a h
  rwa [e4m_N_apply, e4m_N_apply] at this



end LemmaM

section Classify


open Subgroup
open scoped commutatorElement

section Basic

variable {P : Type*} [Group P]

theorem e4c_comm_mul (a x y : P) : ⁅a, x * y⁆ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) := by
  simp only [commutatorElement_def]; group

theorem e4c_comm_of_comm_eq {e x y : P} (h : ⁅e, x⁆ = ⁅e, y⁆) :
    e * (x⁻¹ * y) = (x⁻¹ * y) * e := by
  simp only [commutatorElement_def] at h
  have h1 : x * e⁻¹ * x⁻¹ = y * e⁻¹ * y⁻¹ := by
    calc x * e⁻¹ * x⁻¹ = e⁻¹ * (e * x * e⁻¹ * x⁻¹) := by group
      _ = e⁻¹ * (e * y * e⁻¹ * y⁻¹) := by rw [h]
      _ = y * e⁻¹ * y⁻¹ := by group
  have h2 : x * e * x⁻¹ = y * e * y⁻¹ := by
    calc x * e * x⁻¹ = (x * e⁻¹ * x⁻¹)⁻¹ := by group
      _ = (y * e⁻¹ * y⁻¹)⁻¹ := by rw [h1]
      _ = y * e * y⁻¹ := by group
  calc e * (x⁻¹ * y) = x⁻¹ * (x * e * x⁻¹) * y := by group
    _ = x⁻¹ * (y * e * y⁻¹) * y := by rw [h2]
    _ = (x⁻¹ * y) * e := by group

theorem e4c_card_le_of_fibres [Finite P] (H K D : Subgroup P) (f : H → P)
    (hfD : ∀ x, f x ∈ D) (hfib : ∀ x y : H, f x = f y → (x : P)⁻¹ * y ∈ K) :
    Nat.card H ≤ Nat.card K * Nat.card D := by
  classical
  let r : P → H := fun d => if h : ∃ x, f x = d then h.choose else 1
  have hr : ∀ x : H, f (r (f x)) = f x := by
    intro x
    have h : ∃ y, f y = f x := ⟨x, rfl⟩
    simp only [r, h, ↓reduceDIte]
    exact h.choose_spec
  let g : H → D × K := fun x =>
    (⟨f x, hfD x⟩, ⟨((r (f x) : H) : P)⁻¹ * x, hfib _ _ (hr x)⟩)
  have hg : Function.Injective g := by
    intro x y hxy
    have h1 : f x = f y := by
      have := congrArg (fun t => (t.1 : P)) hxy
      simpa [g] using this
    have h2 := congrArg (fun t => (t.2 : P)) hxy
    simp only [g] at h2
    rw [h1] at h2
    have h3 : (x : P) = y := mul_left_cancel h2
    exact Subtype.ext h3
  have := Nat.card_le_card_of_injective g hg
  rw [Nat.card_prod] at this
  linarith [mul_comm (Nat.card D) (Nat.card K)]

theorem e4c_fibre_comm [Finite P] (B D : Subgroup P)
    (e : P) (hD : ∀ x ∈ B, ⁅e, x⁆ ∈ D) :
    Nat.card B ≤ Nat.card (B ⊓ Subgroup.centralizer {e} : Subgroup P) * Nat.card D := by
  refine e4c_card_le_of_fibres B _ D (fun x => ⁅e, (x : P)⁆) (fun x => hD x x.2) ?_
  intro x y hxy
  have h := e4c_comm_of_comm_eq hxy
  refine ⟨B.mul_mem (B.inv_mem x.2) y.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro h' hh'
  rw [Set.mem_singleton_iff] at hh'
  subst hh'
  exact h

theorem e4c_comm_mem_of_index_three [Finite P] (hP : IsPGroup 3 P) {K N : Subgroup P}
    [K.Normal] [N.Normal] (hKN : K ≤ N) (hcard : Nat.card N = 3 * Nat.card K) :
    ∀ n ∈ N, ∀ g : P, ⁅n, g⁆ ∈ K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 (P ⧸ K)) := ⟨hP.to_quotient K⟩
  let q : P →* P ⧸ K := QuotientGroup.mk' K
  let M : Subgroup (P ⧸ K) := N.map q
  have : M.Normal := Subgroup.Normal.map ‹N.Normal› q (QuotientGroup.mk'_surjective K)
  have hker : (q.domRestrict N).ker = K.subgroupOf N := by
    ext x
    simp [q, Subgroup.mem_subgroupOf]
  have hrange : (q.domRestrict N).range = M := MonoidHom.domRestrict_range N q
  have hkcard : Nat.card (q.domRestrict N).ker = Nat.card K := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  have hMcard : Nat.card M = 3 := by
    have h := Subgroup.card_ker_mul_card_range (q.domRestrict N)
    rw [hkcard, hrange, hcard] at h
    have hK : 0 < Nat.card K := Nat.card_pos
    have : Nat.card K * Nat.card M = Nat.card K * 3 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hK this
  have : Nontrivial M := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hMcard]; norm_num
  obtain ⟨x, hx1, hxc⟩ := CFSG.exists_nontrivial_center_mem_normal (p := 3) (G := P ⧸ K) M
  have hxord : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := hMcard ▸ orderOf_dvd_natCard x
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hzcard : Nat.card (Subgroup.zpowers ((x : P ⧸ K))) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord]
  have hzle : Subgroup.zpowers ((x : P ⧸ K)) ≤ M := Subgroup.zpowers_le.mpr x.2
  have hzeq : Subgroup.zpowers ((x : P ⧸ K)) = M :=
    Subgroup.eq_of_le_of_card_ge hzle (by rw [hzcard, hMcard])
  have hzc : Subgroup.zpowers ((x : P ⧸ K)) ≤ Subgroup.center (P ⧸ K) :=
    Subgroup.zpowers_le.mpr hxc
  intro n hn g
  have hqn : q n ∈ Subgroup.center (P ⧸ K) := hzc (hzeq.symm ▸ Subgroup.mem_map_of_mem q hn)
  have h1 : q ⁅n, g⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_center_iff.mp hqn) (q g)).symm
  have h2 : ⁅n, g⁆ ∈ q.ker := h1
  rwa [show q.ker = K from QuotientGroup.ker_mk' K] at h2

theorem e4c_decomp_aux [Finite P] {E U : Subgroup P}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hUE : U ≤ E) (hcard : Nat.card E = 3 * Nat.card U)
    {e : P} (he : e ∈ E) (heU : e ∉ U) : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s := by
  let W : Subgroup P :=
    { carrier := {z | ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s}
      one_mem' := ⟨1, U.one_mem, 0, by simp⟩
      mul_mem' := by
        rintro a b ⟨v, hv, s, rfl⟩ ⟨v', hv', t, rfl⟩
        refine ⟨v * v', U.mul_mem hv hv', s + t, ?_⟩
        have hc : e ^ s * v' = v' * e ^ s :=
          hEab _ (E.pow_mem he s) _ (hUE hv')
        calc v * e ^ s * (v' * e ^ t) = v * (e ^ s * v') * e ^ t := by group
          _ = v * (v' * e ^ s) * e ^ t := by rw [hc]
          _ = v * v' * e ^ (s + t) := by rw [pow_add]; group
      inv_mem' := by
        rintro a ⟨v, hv, s, rfl⟩
        have hpos : 0 < orderOf e := orderOf_pos e
        refine ⟨v⁻¹, U.inv_mem hv, s * (orderOf e - 1), ?_⟩
        have hc : e ^ s * v⁻¹ = v⁻¹ * e ^ s :=
          hEab _ (E.pow_mem he s) _ (hUE (U.inv_mem hv))
        have hinv : (e ^ s)⁻¹ = e ^ (s * (orderOf e - 1)) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add]
          have : s + s * (orderOf e - 1) = orderOf e * s := by
            rcases Nat.exists_eq_succ_of_ne_zero hpos.ne' with ⟨m, hm⟩
            rw [hm]; simp; ring
          rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
        calc (v * e ^ s)⁻¹ = (e ^ s)⁻¹ * v⁻¹ := by group
          _ = e ^ (s * (orderOf e - 1)) * v⁻¹ := by rw [hinv]
          _ = v⁻¹ * e ^ (s * (orderOf e - 1)) := by
            rw [← hinv]
            have : (e ^ s)⁻¹ * v⁻¹ = v⁻¹ * (e ^ s)⁻¹ := by
              have := hc
              calc (e ^ s)⁻¹ * v⁻¹ = (v * e ^ s)⁻¹ := by group
                _ = (e ^ s * v)⁻¹ := by
                  rw [show v * e ^ s = e ^ s * v from
                    (hEab _ (E.pow_mem he s) _ (hUE hv)).symm]
                _ = v⁻¹ * (e ^ s)⁻¹ := by group
            exact this }
  have hWE : W ≤ E := by
    rintro z ⟨v, hv, s, rfl⟩
    exact E.mul_mem (hUE hv) (E.pow_mem he s)
  have hUW : U ≤ W := fun v hv => ⟨v, hv, 0, by simp⟩
  have heW : e ∈ W := ⟨1, U.one_mem, 1, by simp⟩
  have hd1 : Nat.card U ∣ Nat.card W := Subgroup.card_dvd_of_le hUW
  have hd2 : Nat.card W ∣ Nat.card E := Subgroup.card_dvd_of_le hWE
  have hUpos : 0 < Nat.card U := Nat.card_pos
  obtain ⟨c, hc⟩ := hd1
  rw [hcard, hc] at hd2
  have hc3 : c ∣ 3 := by
    have : Nat.card U * c ∣ Nat.card U * 3 := by rwa [mul_comm 3] at hd2
    exact Nat.dvd_of_mul_dvd_mul_left hUpos this
  have hcc : c = 1 ∨ c = 3 := (Nat.dvd_prime Nat.prime_three).mp hc3
  have hne : W ≠ U := fun h => heU (h ▸ heW)
  have hWcard : Nat.card W = Nat.card E := by
    rcases hcc with rfl | rfl
    · exfalso
      apply hne
      exact (Subgroup.eq_of_le_of_card_ge hUW (by rw [hc]; simp)).symm
    · rw [hcard, hc]; ring
  have hWeq : W = E := Subgroup.eq_of_le_of_card_ge hWE (by rw [hWcard])
  intro z hz
  rw [← hWeq] at hz
  exact hz

end Basic

theorem e4_decomp {P : Type*} [Group P] [Finite P] {E U : Subgroup P}
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hUE : U ≤ E) (hcard : Nat.card E = 3 * Nat.card U)
    {e : P} (he : e ∈ E) (heU : e ∉ U) : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s :=
  e4c_decomp_aux hEab hUE hcard he heU



section Classify

variable {P : Type*} [Group P]

theorem e4c_cent_gen {E U : Subgroup P} {e x : P}
    (hdec : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s)
    (hU : ∀ v ∈ U, x * v = v * x) (he : x * e = e * x) : ∀ z ∈ E, x * z = z * x := by
  intro z hz
  obtain ⟨v, hv, s, rfl⟩ := hdec z hz
  have h1 : Commute x v := hU v hv
  have h2 : Commute x (e ^ s) := (show Commute x e from he).pow_right s
  exact h1.mul_right h2

theorem e4c_central_of_card_three [Finite P] (hP : IsPGroup 3 P) {N : Subgroup P} [N.Normal]
    (hN : Nat.card N = 3) : ∀ n ∈ N, ∀ g : P, g * n = n * g := by
  have h := e4c_comm_mem_of_index_three hP (K := ⊥) (N := N) bot_le
    (by rw [hN, Subgroup.card_bot])
  intro n hn g
  have h' := h n hn g
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h'
  exact h'.symm

structure e4c_Flag (E E₂ E₁ : Subgroup P) (e₂ e₃ : P) : Prop where
  ab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x
  cube : ∀ x ∈ E, x ^ 3 = 1
  le12 : E₁ ≤ E₂
  le2E : E₂ ≤ E
  c1 : Nat.card E₁ = 3
  c2 : Nat.card E₂ = 9
  c3 : Nat.card E = 27
  cen : ∀ z ∈ E₁, ∀ g : P, g * z = z * g
  com2 : ∀ z ∈ E₂, ∀ g : P, ⁅z, g⁆ ∈ E₁
  com3 : ∀ z ∈ E, ∀ g : P, ⁅z, g⁆ ∈ E₂
  e2mem : e₂ ∈ E₂
  e2n : e₂ ∉ E₁
  e3mem : e₃ ∈ E
  e3n : e₃ ∉ E₂

namespace e4c_Flag

variable {E E₂ E₁ : Subgroup P} {e₂ e₃ : P} (F : e4c_Flag E E₂ E₁ e₂ e₃)
include F

section
variable [Finite P]

theorem dec2 : ∀ z ∈ E₂, ∃ v ∈ E₁, ∃ s : ℕ, z = v * e₂ ^ s :=
  e4_decomp (fun x hx y hy => F.ab x (F.le2E hx) y (F.le2E hy)) F.le12
    (by rw [F.c1, F.c2]) F.e2mem F.e2n

theorem dec3 : ∀ z ∈ E, ∃ v ∈ E₂, ∃ s : ℕ, z = v * e₃ ^ s :=
  e4_decomp F.ab F.le2E (by rw [F.c2, F.c3]) F.e3mem F.e3n

end

theorem cent2 [Finite P] {x : P} (hx : x * e₂ = e₂ * x) : ∀ z ∈ E₂, x * z = z * x :=
  e4c_cent_gen F.dec2 (fun v hv => F.cen v hv x) hx

theorem cent3 [Finite P] {x : P} (h2 : ∀ z ∈ E₂, x * z = z * x) (h3 : x * e₃ = e₃ * x) :
    ∀ z ∈ E, x * z = z * x :=
  e4c_cent_gen F.dec3 h2 h3

theorem mem_of_cent [Finite P]
    (hI : ∀ x : P, (∀ e ∈ E, x * e = e * x) → x ^ 3 = 1 → x ∈ E)
    {x : P} (h2 : x * e₂ = e₂ * x) (h3 : x * e₃ = e₃ * x) (hx3 : x ^ 3 = 1) : x ∈ E :=
  hI x (F.cent3 (F.cent2 h2) h3) hx3

theorem bound_i [Finite P] (B : Subgroup P) (hB : Nat.card B = 81) :
    81 ≤ Nat.card (B ⊓ Subgroup.centralizer {e₂} : Subgroup P) * 3 := by
  have := e4c_fibre_comm B E₁ e₂ (fun x _ => F.com2 e₂ F.e2mem x)
  rw [F.c1, hB] at this
  exact this

theorem fibre2 [Finite P]
    (hI : ∀ x : P, (∀ e ∈ E, x * e = e * x) → x ^ 3 = 1 → x ∈ E)
    (B : Subgroup P) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (H D : Subgroup P) (hHB : H ≤ B) (hH2 : ∀ x ∈ H, x * e₂ = e₂ * x)
    (hD : ∀ x ∈ H, ⁅e₃, x⁆ ∈ D) :
    Nat.card H ≤ Nat.card (B ⊓ E : Subgroup P) * Nat.card D := by
  refine e4c_card_le_of_fibres H _ D (fun x => ⁅e₃, (x : P)⁆) (fun x => hD x x.2) ?_
  intro x y hxy
  have h := e4c_comm_of_comm_eq hxy
  have hxyH : (x : P)⁻¹ * y ∈ H := H.mul_mem (H.inv_mem x.2) y.2
  have hc2 : Commute ((x : P)⁻¹ * y) e₂ :=
    (Commute.inv_left (show Commute (x : P) e₂ from hH2 x x.2)).mul_left
      (show Commute (y : P) e₂ from hH2 y y.2)
  have hmem : (x : P)⁻¹ * y ∈ E :=
    F.mem_of_cent hI hc2 h.symm (hB3 _ (hHB hxyH))
  exact ⟨hHB hxyH, hmem⟩

theorem claim [Finite P]
    (B : Subgroup P) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    {x₀ : P} (hx₀B : x₀ ∈ B) (hx₀ : ¬ x₀ * e₂ = e₂ * x₀)
    {ψ : P} (hψB : ψ ∈ B) (hψ2 : ψ * e₂ = e₂ * ψ) : ⁅e₃, ψ⁆ ∈ E₁ := by
  have ha : ⁅e₃, x₀⁆ ∈ E₂ := F.com3 e₃ F.e3mem x₀
  have hw : ⁅e₃, ψ⁆ ∈ E₂ := F.com3 e₃ F.e3mem ψ
  have hψa : ψ * ⁅e₃, x₀⁆ = ⁅e₃, x₀⁆ * ψ := F.cent2 hψ2 _ ha
  have hcomm : x₀ * ψ = ψ * x₀ := hBab _ hx₀B _ hψB
  have e1 : ⁅e₃, x₀ * ψ⁆ = ⁅e₃, x₀⁆ * (x₀ * ⁅e₃, ψ⁆ * x₀⁻¹) := e4c_comm_mul _ _ _
  have e2 : ⁅e₃, ψ * x₀⁆ = ⁅e₃, ψ⁆ * (ψ * ⁅e₃, x₀⁆ * ψ⁻¹) := e4c_comm_mul _ _ _
  have e3 : ψ * ⁅e₃, x₀⁆ * ψ⁻¹ = ⁅e₃, x₀⁆ := by rw [hψa]; group
  have hwa : ⁅e₃, ψ⁆ * ⁅e₃, x₀⁆ = ⁅e₃, x₀⁆ * ⁅e₃, ψ⁆ :=
    F.ab _ (F.le2E hw) _ (F.le2E ha)
  have h4 : ⁅e₃, x₀⁆ * (x₀ * ⁅e₃, ψ⁆ * x₀⁻¹) = ⁅e₃, x₀⁆ * ⁅e₃, ψ⁆ := by
    rw [← e1, hcomm, e2, e3, hwa]
  have h5 : x₀ * ⁅e₃, ψ⁆ * x₀⁻¹ = ⁅e₃, ψ⁆ := mul_left_cancel h4
  have h6 : x₀ * ⁅e₃, ψ⁆ = ⁅e₃, ψ⁆ * x₀ := by
    rw [mul_inv_eq_iff_eq_mul] at h5; exact h5
  obtain ⟨v, hv, j, hj⟩ := F.dec2 _ hw
  have h7 : x₀ * e₂ ^ j = e₂ ^ j * x₀ := by
    have hvx : x₀ * v = v * x₀ := F.cen v hv x₀
    rw [hj] at h6
    have : v * (x₀ * e₂ ^ j) = v * (e₂ ^ j * x₀) := by
      calc v * (x₀ * e₂ ^ j) = (v * x₀) * e₂ ^ j := by group
        _ = (x₀ * v) * e₂ ^ j := by rw [hvx]
        _ = x₀ * (v * e₂ ^ j) := by group
        _ = (v * e₂ ^ j) * x₀ := h6
        _ = v * (e₂ ^ j * x₀) := by group
    exact mul_left_cancel this
  set c := ⁅e₂, x₀⁆ with hcdef
  have hcE₁ : c ∈ E₁ := F.com2 e₂ F.e2mem x₀
  have hc1 : c⁻¹ ≠ 1 := by
    intro h
    apply hx₀
    have : c = 1 := inv_eq_one.mp h
    rw [hcdef, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hcinv : c⁻¹ ∈ E₁ := E₁.inv_mem hcE₁
  have hc3 : (c⁻¹) ^ 3 = 1 := F.cube _ (F.le2E (F.le12 hcinv))
  have hconj : x₀ * e₂ * x₀⁻¹ = c⁻¹ * e₂ := by
    rw [hcdef]; simp only [commutatorElement_def]; group
  have hcomc : Commute (c⁻¹) e₂ := (show e₂ * c⁻¹ = c⁻¹ * e₂ from F.cen _ hcinv e₂).symm
  have h8 : (c⁻¹) ^ j * e₂ ^ j = e₂ ^ j := by
    calc (c⁻¹) ^ j * e₂ ^ j = (c⁻¹ * e₂) ^ j := (hcomc.mul_pow j).symm
      _ = (x₀ * e₂ * x₀⁻¹) ^ j := by rw [hconj]
      _ = x₀ * e₂ ^ j * x₀⁻¹ := conj_pow
      _ = e₂ ^ j := by rw [h7]; group
  have h9 : (c⁻¹) ^ j = 1 := by
    have : (c⁻¹) ^ j * e₂ ^ j = 1 * e₂ ^ j := by rw [h8, one_mul]
    exact mul_right_cancel this
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (c⁻¹) = 3 := orderOf_eq_prime hc3 hc1
  have hdvd : 3 ∣ j := hord ▸ orderOf_dvd_iff_pow_eq_one.mpr h9
  obtain ⟨m, hm⟩ := hdvd
  have hej : e₂ ^ j = 1 := by
    rw [hm, pow_mul, F.cube _ (F.le2E F.e2mem), one_pow]
  rw [hj, hej, mul_one]
  exact hv

theorem bound_ii [Finite P]
    (hI : ∀ x : P, (∀ e ∈ E, x * e = e * x) → x ^ 3 = 1 → x ∈ E)
    (B : Subgroup P) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hB : Nat.card B = 81) : 81 ≤ 9 * Nat.card (B ⊓ E : Subgroup P) := by
  have h1 := F.bound_i B hB
  by_cases hA : ∀ x ∈ B, x * e₂ = e₂ * x
  · have h2 := F.fibre2 hI B hB3 B E₂ le_rfl hA (fun x _ => F.com3 e₃ F.e3mem x)
    rw [F.c2, hB] at h2
    linarith
  · push Not at hA
    obtain ⟨x₀, hx₀B, hx₀⟩ := hA
    have hmem : ∀ ψ ∈ (B ⊓ Subgroup.centralizer {e₂} : Subgroup P), ψ ∈ B ∧ ψ * e₂ = e₂ * ψ := by
      intro ψ hψ
      refine ⟨hψ.1, ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp hψ.2 e₂ rfl).symm
    have h2 := F.fibre2 hI B hB3 (B ⊓ Subgroup.centralizer {e₂}) E₁ inf_le_left
      (fun x hx => (hmem x hx).2)
      (fun x hx => F.claim B hBab hx₀B hx₀ (hmem x hx).1 (hmem x hx).2)
    rw [F.c1] at h2
    linarith

theorem inter_eq [Finite P]
    (hI : ∀ x : P, (∀ e ∈ E, x * e = e * x) → x ^ 3 = 1 → x ∈ E)
    (B : Subgroup P) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hB : Nat.card B = 81) : B ⊓ E = E₂ := by
  have hii := F.bound_ii hI B hBab hB3 hB
  have hdvd : Nat.card (B ⊓ E : Subgroup P) ∣ 27 := by
    rw [← F.c3]; exact Subgroup.card_dvd_of_le inf_le_right
  have hle27 : Nat.card (B ⊓ E : Subgroup P) ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : Nat.card (B ⊓ E : Subgroup P) = 9 ∨ Nat.card (B ⊓ E : Subgroup P) = 27 := by
    generalize Nat.card (B ⊓ E : Subgroup P) = t at hii hdvd hle27
    interval_cases t <;> omega
  rcases hcases with h9 | h27
  ·
    have hb1 := F.bound_i B hB
    have hUle : (B ⊓ E : Subgroup P) ≤ (B ⊓ Subgroup.centralizer {e₂} : Subgroup P) := by
      intro x hx
      refine ⟨hx.1, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      subst hh'
      exact F.ab _ (F.le2E F.e2mem) _ hx.2
    obtain ⟨ψ, hψ, hψU⟩ : ∃ ψ ∈ (B ⊓ Subgroup.centralizer {e₂} : Subgroup P),
        ψ ∉ (B ⊓ E : Subgroup P) := by
      by_contra hcon
      push Not at hcon
      have hsub : (B ⊓ Subgroup.centralizer {e₂} : Subgroup P) ≤ (B ⊓ E : Subgroup P) := hcon
      have := Subgroup.card_le_of_le hsub
      omega
    have hψB : ψ ∈ B := hψ.1
    have hψ2 : ψ * e₂ = e₂ * ψ := (Subgroup.mem_centralizer_iff.mp hψ.2 e₂ rfl).symm
    have hψE : ψ ∉ E := fun h => hψU ⟨hψB, h⟩
    have hψ3 : ¬ ψ * e₃ = e₃ * ψ := fun h => hψE (F.mem_of_cent hI hψ2 h (hB3 ψ hψB))
    have hsubE₂ : (B ⊓ E : Subgroup P) ≤ E₂ := by
      intro u hu
      obtain ⟨w, hw, k, rfl⟩ := F.dec3 u hu.2
      have hψw : ψ * w = w * ψ := F.cent2 hψ2 w hw
      have hψu : ψ * (w * e₃ ^ k) = (w * e₃ ^ k) * ψ := hBab _ hψB _ hu.1
      have hψk : Commute ψ (e₃ ^ k) := by
        have : e₃ ^ k = w⁻¹ * (w * e₃ ^ k) := by group
        rw [this]
        exact (Commute.inv_right (show Commute ψ w from hψw)).mul_right
          (show Commute ψ (w * e₃ ^ k) from hψu)
      have he3cube : e₃ ^ 3 = 1 := F.cube _ F.e3mem
      have hmod : e₃ ^ k = e₃ ^ (k % 3) := pow_eq_pow_mod k he3cube
      have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases hk3 with h0 | h1 | h2
      · rw [h0] at hmod
        rw [hmod, pow_zero, mul_one]
        exact hw
      · exfalso
        rw [h1, pow_one] at hmod
        rw [hmod] at hψk
        exact hψ3 hψk
      · exfalso
        rw [h2] at hmod
        rw [hmod] at hψk
        have h4 : Commute ψ ((e₃ ^ 2) ^ 2) := hψk.pow_right 2
        have : (e₃ ^ 2) ^ 2 = e₃ := by
          calc (e₃ ^ 2) ^ 2 = e₃ ^ 3 * e₃ := by group
            _ = e₃ := by rw [he3cube, one_mul]
        rw [this] at h4
        exact hψ3 h4
    exact Subgroup.eq_of_le_of_card_ge hsubE₂ (by rw [F.c2, h9])
  ·
    exfalso
    have hEq : (B ⊓ E : Subgroup P) = E :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [F.c3, h27])
    have hEB : E ≤ B := by rw [← hEq]; exact inf_le_left
    have hBE : B ≤ E := by
      intro x hx
      exact hI x (fun e he => hBab x hx e (hEB he)) (hB3 x hx)
    have := Subgroup.card_le_of_le hBE
    rw [hB, F.c3] at this
    omega

theorem surj [Finite P]
    (hI : ∀ x : P, (∀ e ∈ E, x * e = e * x) → x ^ 3 = 1 → x ∈ E)
    (B : Subgroup P) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hB : Nat.card B = 81) :
    ∀ e ∈ E, e ∉ E₂ → ∀ u ∈ E₂, ∃ x ∈ B, ⁅e, x⁆ = u := by
  have hBE := F.inter_eq hI B hBab hB3 hB
  have hE2B : E₂ ≤ B := by rw [← hBE]; exact inf_le_left
  intro e he heU
  let θ : B →* E₂ :=
    { toFun := fun x => ⟨⁅e, (x : P)⁆, F.com3 e he x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        show ⁅e, ((x : P) * (y : P))⁆ = ⁅e, (x : P)⁆ * ⁅e, (y : P)⁆
        rw [e4c_comm_mul]
        have := hBab x x.2 ⁅e, (y : P)⁆ (hE2B (F.com3 e he y))
        rw [this, mul_inv_cancel_right] }
  have hdec : ∀ z ∈ E, ∃ v ∈ E₂, ∃ s : ℕ, z = v * e ^ s :=
    e4_decomp F.ab F.le2E (by rw [F.c2, F.c3]) he heU
  have hker : θ.ker = E₂.subgroupOf B := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : ⁅e, (x : P)⁆ = 1 := congrArg Subtype.val h
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      have hxE : (x : P) ∈ E := by
        refine hI x ?_ (hB3 x x.2)
        exact e4c_cent_gen hdec (fun v hv => hBab x x.2 v (hE2B hv)) h1.symm
      have : (x : P) ∈ B ⊓ E := ⟨x.2, hxE⟩
      rwa [hBE] at this
    · intro h
      apply Subtype.ext
      show ⁅e, (x : P)⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact F.ab e he x (F.le2E h)
  have hkcard : Nat.card θ.ker = 9 := by
    rw [hker, ← F.c2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE2B).toEquiv
  have hmul := Subgroup.card_ker_mul_card_range θ
  rw [hkcard, hB] at hmul
  have hrcard : Nat.card θ.range = Nat.card E₂ := by
    rw [F.c2]; omega
  have htop : θ.range = ⊤ := Subgroup.eq_top_of_card_eq _ hrcard
  intro u hu
  have hmem : (⟨u, hu⟩ : E₂) ∈ θ.range := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

end e4c_Flag

end Classify

theorem e4c_card27 {P : Type*} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (E : Subgroup P) [E.Normal] (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hEcard : Nat.card E ≤ 27)
    (hI : ∀ x : P, (∀ e ∈ E, x * e = e * x) → x ^ 3 = 1 → x ∈ E)
    (B₀ : Subgroup P) (hB₀3 : ∀ x ∈ B₀, x ^ 3 = 1)
    (hB₀ : Nat.card B₀ = 81) : Nat.card E = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨hP⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hP.to_subgroup E)
  have hn4 : n < 4 := by
    by_contra hcon
    have h4 : 3 ^ 4 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hBE : (∀ x ∈ B₀, ∀ e ∈ E, x * e = e * x) → B₀ ≤ E := fun h x hx =>
    hI x (fun e he => h x hx e he) (hB₀3 x hx)
  interval_cases n
  · exfalso
    have hbot : E = ⊥ := Subgroup.eq_bot_of_card_eq E (by simpa using hn)
    have hle : B₀ ≤ E := hBE (by
      intro x hx e he
      rw [hbot, Subgroup.mem_bot] at he
      rw [he]; simp)
    have := Subgroup.card_le_of_le hle
    omega
  · exfalso
    have hcen := e4c_central_of_card_three hP (N := E) (by simpa using hn)
    have hle : B₀ ≤ E := hBE (fun x _ e he => (hcen e he x))
    have := Subgroup.card_le_of_le hle
    omega
  · exfalso
    obtain ⟨E₁, hE₁n, hE₁E, hE₁c⟩ :=
      CFSG.exists_normal_subgroup_card_pow_of_normal (p := 3) E inferInstance hn 1 (by norm_num)
    have hE₁c' : Nat.card E₁ = 3 := by simpa using hE₁c
    have hE9 : Nat.card E = 9 := by simpa using hn
    have hcen := e4c_central_of_card_three hP (N := E₁) hE₁c'
    have hcom := e4c_comm_mem_of_index_three hP (K := E₁) (N := E) hE₁E (by rw [hE9, hE₁c'])
    obtain ⟨e₂, he₂, he₂n⟩ : ∃ e₂ ∈ E, e₂ ∉ E₁ := by
      by_contra hcon
      push Not at hcon
      have := Subgroup.card_le_of_le (show E ≤ E₁ from hcon)
      omega
    have hdec : ∀ z ∈ E, ∃ v ∈ E₁, ∃ s : ℕ, z = v * e₂ ^ s :=
      e4_decomp hEab hE₁E (by rw [hE9, hE₁c']) he₂ he₂n
    have hfib := e4c_fibre_comm B₀ E₁ e₂ (fun x _ => hcom e₂ he₂ x)
    have hle : (B₀ ⊓ Subgroup.centralizer {e₂} : Subgroup P) ≤ E := by
      intro x hx
      have hxe : x * e₂ = e₂ * x :=
        (Subgroup.mem_centralizer_iff.mp hx.2 e₂ rfl).symm
      exact hI x (e4c_cent_gen hdec (fun v hv => hcen v hv x) hxe) (hB₀3 x hx.1)
    have h1 := Subgroup.card_le_of_le hle
    rw [hE₁c', hB₀] at hfib
    omega
  · rw [hn]; norm_num


theorem e4_classify {P : Type*} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (E : Subgroup P) [E.Normal]
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hEcard : Nat.card E ≤ 27)
    (hI : ∀ x : P, (∀ e ∈ E, x * e = e * x) → x ^ 3 = 1 → x ∈ E)
    (B₀ : Subgroup P) (_hB₀ab : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x) (hB₀3 : ∀ x ∈ B₀, x ^ 3 = 1)
    (hB₀ : Nat.card B₀ = 81) :
    Nat.card E = 27 ∧ ∃ U : Subgroup P, U.Normal ∧ U ≤ E ∧ Nat.card U = 9 ∧
      (∀ z ∈ E, ∀ g : P, ⁅z, g⁆ ∈ U) ∧
      ∀ B : Subgroup P, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x ^ 3 = 1) →
        Nat.card B = 81 → B ⊓ E = U ∧
          ∀ e ∈ E, e ∉ U → ∀ u ∈ U, ∃ x ∈ B, ⁅e, x⁆ = u := by
  have hc27 : Nat.card E = 27 := e4c_card27 hP E hEab hEcard hI B₀ hB₀3 hB₀
  refine ⟨hc27, ?_⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨hP⟩
  obtain ⟨E₂, hE₂n, hE₂E, hE₂c⟩ :=
    CFSG.exists_normal_subgroup_card_pow_of_normal (p := 3) E inferInstance
      (k := 3) (by rw [hc27]; norm_num) 2 (by norm_num)
  have hE₂c' : Nat.card E₂ = 9 := by simpa using hE₂c
  obtain ⟨E₁, hE₁n, hE₁E₂, hE₁c⟩ :=
    CFSG.exists_normal_subgroup_card_pow_of_normal (p := 3) E₂ hE₂n
      (k := 2) (by simpa using hE₂c') 1 (by norm_num)
  have hE₁c' : Nat.card E₁ = 3 := by simpa using hE₁c
  have hcen := e4c_central_of_card_three hP (N := E₁) hE₁c'
  have hcom2 := e4c_comm_mem_of_index_three hP (K := E₁) (N := E₂) hE₁E₂
    (by rw [hE₂c', hE₁c'])
  have hcom3 := e4c_comm_mem_of_index_three hP (K := E₂) (N := E) hE₂E
    (by rw [hc27, hE₂c'])
  obtain ⟨e₂, he₂, he₂n⟩ : ∃ e₂ ∈ E₂, e₂ ∉ E₁ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show E₂ ≤ E₁ from hcon)
    omega
  obtain ⟨e₃, he₃, he₃n⟩ : ∃ e₃ ∈ E, e₃ ∉ E₂ := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show E ≤ E₂ from hcon)
    omega
  have F : e4c_Flag E E₂ E₁ e₂ e₃ :=
    { ab := hEab, cube := hE3, le12 := hE₁E₂, le2E := hE₂E, c1 := hE₁c', c2 := hE₂c'
      c3 := hc27, cen := hcen, com2 := hcom2, com3 := hcom3, e2mem := he₂, e2n := he₂n
      e3mem := he₃, e3n := he₃n }
  refine ⟨E₂, hE₂n, hE₂E, hE₂c', hcom3, ?_⟩
  intro B hBab hB3 hB
  exact ⟨F.inter_eq hI B hBab hB3 hB, F.surj hI B hBab hB3 hB⟩



end Classify

section Uniq


open Subgroup
open scoped commutatorElement

def e4u_c {P : Type*} [Group P] (a b : P) : P := a⁻¹ * b⁻¹ * a * b

local notation "bk(" a ", " b ")" => e4u_c a b

theorem e4u_c_eq_mathlib {P : Type*} [Group P] (a b : P) : bk(a, b) = ⁅a⁻¹, b⁻¹⁆ := by
  simp only [e4u_c, commutatorElement_def, inv_inv]

theorem e4u_c_eq_one_iff {P : Type*} [Group P] (a b : P) : bk(a, b) = 1 ↔ a * b = b * a := by
  constructor
  · intro h
    calc a * b = b * a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = b * a := by rw [show a⁻¹ * b⁻¹ * a * b = 1 from h, mul_one]
  · intro h
    calc a⁻¹ * b⁻¹ * a * b = (b * a)⁻¹ * (a * b) := by group
      _ = 1 := by rw [← h, inv_mul_cancel]

theorem e4u_pow3 {P : Type*} [Group P] (x y t : P) (hyx : y * x = x * y * t)
    (hxt' : x * t = t * x) (hyt' : y * t = t * y) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 * t ^ 3 := by
  have hxt : t * x = x * t := hxt'.symm
  have hyt : t * y = y * t := hyt'.symm
  have hxt2 : ∀ r, t * (x * r) = x * (t * r) := fun r => by
    rw [← mul_assoc, hxt, mul_assoc]
  have hyt2 : ∀ r, t * (y * r) = y * (t * r) := fun r => by
    rw [← mul_assoc, hyt, mul_assoc]
  have hyx2 : ∀ r, y * (x * r) = x * (y * (t * r)) := fun r => by
    rw [← mul_assoc, hyx]; simp only [mul_assoc]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc, hyx2, hxt2, hyt, hyt2]

theorem e4u_conj_cent {P : Type*} [Group P] {x u : P} (h : x * u = u * x) :
    x⁻¹ * u * x = u := by
  rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem e4u_conj_pow3 {P : Type*} [Group P] (a b : P) :
    (a * b * a⁻¹) ^ 3 = a * b ^ 3 * a⁻¹ := by
  simp only [pow_succ, pow_zero, one_mul]; group

theorem e4u_partner {P : Type*} [Group P] (U : Subgroup P) (hUcard : Nat.card U = 9)
    (hU3 : ∀ x ∈ U, x ^ 3 = 1) (u : P) (hu : u ∈ U) (hu1 : u ≠ 1) :
    ∃ v ∈ U, ∀ s t : ℕ, u ^ s * v ^ t = 1 → 3 ∣ s ∧ 3 ∣ t := by
  have hord : orderOf u = 3 := orderOf_eq_prime (hU3 u hu) hu1
  have hfin : Finite (zpowers u) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_zpowers, hord]; norm_num
  have hUfin : Finite U := Nat.finite_of_card_ne_zero (by rw [hUcard]; norm_num)
  obtain ⟨v, hvU, hvn⟩ : ∃ v ∈ U, v ∉ zpowers u := by
    by_contra hcon
    push Not at hcon
    have hle : U ≤ zpowers u := fun v hv => hcon v hv
    have := Subgroup.card_le_of_le hle
    rw [hUcard, Nat.card_zpowers, hord] at this
    omega
  refine ⟨v, hvU, fun s t hst => ?_⟩
  have hv3 := hU3 v hvU
  have hvt : v ^ t = (u ^ s)⁻¹ := eq_inv_of_mul_eq_one_right hst
  by_cases h3 : 3 ∣ t
  · obtain ⟨k, rfl⟩ := h3
    have h1 : v ^ (3 * k) = 1 := by rw [pow_mul, hv3, one_pow]
    rw [h1, mul_one] at hst
    exact ⟨hord ▸ orderOf_dvd_of_pow_eq_one hst, dvd_mul_right 3 k⟩
  · exfalso
    have hmod : t * t % 3 = 1 := by
      have : t % 3 = 1 ∨ t % 3 = 2 := by omega
      rcases this with h | h <;> simp [Nat.mul_mod, h]
    have hvv : (v ^ t) ^ t = v := by
      rw [← pow_mul]
      have := Nat.div_add_mod (t * t) 3
      rw [hmod] at this
      rw [← this, pow_add, pow_mul, hv3, one_pow, one_mul, pow_one]
    apply hvn
    rw [← hvv, hvt]
    exact Subgroup.pow_mem _ (inv_mem (pow_mem (mem_zpowers u) s)) t

theorem e4u_comm_mul {P : Type*} [Group P] (z z' x : P) (h : bk(z, x) * z' = z' * bk(z, x)) :
    bk(z * z', x) = bk(z, x) * bk(z', x) := by
  have h' : z'⁻¹ * bk(z, x) = bk(z, x) * z'⁻¹ :=
    (Commute.inv_right (show Commute bk(z, x) z' from h)).eq.symm
  calc bk(z * z', x) = z'⁻¹ * bk(z, x) * (x⁻¹ * z' * x) := by
        simp only [e4u_c]; group
    _ = bk(z, x) * z'⁻¹ * (x⁻¹ * z' * x) := by rw [h']
    _ = bk(z, x) * bk(z', x) := by simp only [e4u_c]; group

theorem e4u_theta_mul {P : Type*} [Group P] (E : Subgroup P)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (x : P) (hΘ : ∀ z ∈ E, bk(z, x) ∈ E)
    (z z' : P) (hz : z ∈ E) (hz' : z' ∈ E) : bk(z * z', x) = bk(z, x) * bk(z', x) :=
  e4u_comm_mul z z' x (hEc _ (hΘ z hz) z' hz')

theorem e4u_theta_pow {P : Type*} [Group P] (E : Subgroup P)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (x : P) (hΘ : ∀ z ∈ E, bk(z, x) ∈ E)
    (z : P) (hz : z ∈ E) (n : ℕ) : bk(z ^ n, x) = bk(z, x) ^ n := by
  induction n with
  | zero => simp [e4u_c]
  | succ n ih =>
    rw [pow_succ, e4u_theta_mul E hEc x hΘ _ _ (pow_mem hz n) hz, ih, pow_succ]

theorem e4u_CT {P : Type*} [Group P] (E U : Subgroup P) (e : P)
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hUE : U ≤ E) (heE : e ∈ E)
    (hdec : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s)
    (hflag : ∀ z ∈ E, ∀ g : P, bk(z, g) ∈ U) (x1 x2 : P)
    (hx1 : ∀ u ∈ U, x1 * u = u * x1) (hx2 : ∀ u ∈ U, x2 * u = u * x2)
    (hind : ∀ s t : ℕ, bk(e, x1) ^ s * bk(e, x2) ^ t = 1 → 3 ∣ s ∧ 3 ∣ t)
    (d1 d2 : P) (hd1 : d1 ∈ E) (hd2 : d2 ∈ E) (hd : bk(d2, x1) = bk(d1, x2)) :
    d1 ∈ U ∧ d2 ∈ U := by
  have key : ∀ x : P, (∀ u ∈ U, x * u = u * x) → ∀ v ∈ U, ∀ s : ℕ,
      bk(v * e ^ s, x) = bk(e, x) ^ s := by
    intro x hx v hv s
    have hΘ : ∀ z ∈ E, bk(z, x) ∈ E := fun z hz => hUE (hflag z hz x)
    rw [e4u_theta_mul E hEc x hΘ v _ (hUE hv) (pow_mem heE s), e4u_theta_pow E hEc x hΘ e heE s,
      (e4u_c_eq_one_iff v x).mpr (hx v hv).symm, one_mul]
  have he : ∀ s : ℕ, 3 ∣ s → e ^ s = 1 := by
    intro s ⟨k, hk⟩
    rw [hk, pow_mul, hE3 e heE, one_pow]
  obtain ⟨v1, hv1, s1, rfl⟩ := hdec d1 hd1
  obtain ⟨v2, hv2, s2, rfl⟩ := hdec d2 hd2
  rw [key x1 hx1 v2 hv2, key x2 hx2 v1 hv1] at hd
  have hq3 : bk(e, x2) ^ 3 = 1 := hE3 _ (hUE (hflag e heE x2))
  have h1 : bk(e, x1) ^ s2 * bk(e, x2) ^ (2 * s1) = 1 := by
    rw [hd, ← pow_add, show s1 + 2 * s1 = 3 * s1 by ring, pow_mul, hq3, one_pow]
  obtain ⟨h2, h3⟩ := hind _ _ h1
  have h4 : 3 ∣ s1 := by omega
  rw [he s1 h4, mul_one]
  rw [he s2 h2, mul_one]
  exact ⟨hv1, hv2⟩

theorem e4u_cent_E {P : Type*} [Group P] (E U : Subgroup P) (e : P)
    (hdec : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s) (w : P)
    (hwe : w * e = e * w) (hwU : ∀ u ∈ U, w * u = u * w) : ∀ z ∈ E, w * z = z * w := by
  intro z hz
  obtain ⟨v, hv, s, rfl⟩ := hdec z hz
  exact (Commute.mul_right (hwU v hv) ((show Commute w e from hwe).pow_right s)).eq

theorem e4u_partner_B {P : Type*} [Group P] (E U B : Subgroup P) (e : P)
    (hUcard : Nat.card U = 9) (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hUE : U ≤ E) (heE : e ∈ E)
    (hdec : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s)
    (hflag : ∀ z ∈ E, ∀ g : P, bk(z, g) ∈ U)
    (hI : ∀ x : P, (∀ z ∈ E, x * z = z * x) → x ^ 3 = 1 → x ∈ E)
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hBU : B ⊓ E = U) (hBsurj : ∀ u ∈ U, ∃ x ∈ B, bk(e, x) = u) :
    ∀ x ∈ B, x ∉ U → ∃ x' ∈ B,
      ∀ s t : ℕ, bk(e, x) ^ s * bk(e, x') ^ t = 1 → 3 ∣ s ∧ 3 ∣ t := by
  intro x hx hxU
  have hUB : U ≤ B := fun u hu => by
    have : u ∈ B ⊓ E := by rw [hBU]; exact hu
    exact this.1
  have hp1 : bk(e, x) ≠ 1 := by
    intro h
    apply hxU
    have hex : x * e = e * x := ((e4u_c_eq_one_iff e x).mp h).symm
    have hxE := hI x (e4u_cent_E E U e hdec x hex (fun u hu => hBab x hx u (hUB hu)))
      (hB3 x hx)
    rw [← hBU]
    exact ⟨hx, hxE⟩
  obtain ⟨v, hv, hind⟩ := e4u_partner U hUcard (fun u hu => hE3 u (hUE hu)) bk(e, x)
    (hflag e heE x) hp1
  obtain ⟨x', hx', hxx'⟩ := hBsurj v hv
  refine ⟨x', hx', ?_⟩
  rw [hxx']
  exact hind

theorem e4u_core {P : Type*} [Group P] (E U A B B' : Subgroup P) (e : P) [A.Normal]
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAcent : ∀ g : P, (∀ a ∈ A, g * a = a * g) → g ∈ A)
    (hEA : E ≤ A) (hAE : ∀ a ∈ A, a ^ 3 = 1 → a ∈ E)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hUE : U ≤ E) (hUcard : Nat.card U = 9)
    (heE : e ∈ E)
    (hdec : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s)
    (hflag : ∀ z ∈ E, ∀ g : P, bk(z, g) ∈ U)
    (hI : ∀ x : P, (∀ z ∈ E, x * z = z * x) → x ^ 3 = 1 → x ∈ E)
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hBU : B ⊓ E = U)
    (hBsurj : ∀ u ∈ U, ∃ x ∈ B, bk(e, x) = u)
    (hBG : ∀ x ∈ B, ∀ a ∈ A, bk(a, x) ∈ U)
    (hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x) (hB'3 : ∀ x ∈ B', x ^ 3 = 1)
    (hB'U : B' ⊓ E = U)
    (hB'surj : ∀ u ∈ U, ∃ x ∈ B', bk(e, x) = u)
    (hB'G : ∀ x ∈ B', ∀ a ∈ A, bk(a, x) ∈ U) :
    B' ≤ B := by
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy => hAab x (hEA hx) y (hEA hy)
  have hUB : U ≤ B := fun u hu => by
    have : u ∈ B ⊓ E := by rw [hBU]; exact hu
    exact this.1
  have hUB' : U ≤ B' := fun u hu => by
    have : u ∈ B' ⊓ E := by rw [hB'U]; exact hu
    exact this.1
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := fun u hu => hE3 u (hUE hu)
  have hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := fun u hu v hv => hEc u (hUE hu) v (hUE hv)
  have hBc : ∀ x ∈ B, ∀ u ∈ U, x * u = u * x := fun x hx u hu => hBab x hx u (hUB hu)
  have hB'c : ∀ x ∈ B', ∀ u ∈ U, x * u = u * x := fun x hx u hu => hB'ab x hx u (hUB' hu)
  have hpartB := e4u_partner_B E U B e hUcard hE3 hUE heE hdec hflag hI hBab hB3 hBU hBsurj
  have hpartB' := e4u_partner_B E U B' e hUcard hE3 hUE heE hdec hflag hI hB'ab hB'3 hB'U hB'surj
  have S1 : ∀ x ∈ B, ∀ y ∈ B', bk(y, x) ∈ A := by
    intro x hx y hy
    have key : ∀ a ∈ A, (x * y)⁻¹ * a * (x * y) = (y * x)⁻¹ * a * (y * x) := by
      intro a ha
      have hux : bk(a, x) ∈ U := hBG x hx a ha
      have huy : bk(a, y) ∈ U := hB'G y hy a ha
      have e1 : x⁻¹ * a * x = a * bk(a, x) := by simp only [e4u_c]; group
      have e2 : y⁻¹ * a * y = a * bk(a, y) := by simp only [e4u_c]; group
      calc (x * y)⁻¹ * a * (x * y) = y⁻¹ * (x⁻¹ * a * x) * y := by group
        _ = y⁻¹ * (a * bk(a, x)) * y := by rw [e1]
        _ = (y⁻¹ * a * y) * (y⁻¹ * bk(a, x) * y) := by group
        _ = a * (bk(a, y) * bk(a, x)) := by
          rw [e2, e4u_conj_cent (hB'c y hy _ hux), mul_assoc]
        _ = a * (bk(a, x) * bk(a, y)) := by rw [hUc _ huy _ hux]
        _ = (x⁻¹ * a * x) * (x⁻¹ * bk(a, y) * x) := by
          rw [e1, e4u_conj_cent (hBc x hx _ huy), mul_assoc]
        _ = x⁻¹ * (y⁻¹ * a * y) * x := by
          rw [e2]; group
        _ = (y * x)⁻¹ * a * (y * x) := by group
    apply hAcent
    intro a ha
    have ha' : (x * y) * a * (x * y)⁻¹ ∈ A := ‹A.Normal›.conj_mem a ha (x * y)
    have key' : a = (y * x)⁻¹ * ((x * y) * a * (x * y)⁻¹) * (y * x) := by
      have := key _ ha'
      rw [← this]; group
    calc bk(y, x) * a
        = bk(y, x) * ((y * x)⁻¹ * ((x * y) * a * (x * y)⁻¹) * (y * x)) := by rw [← key']
      _ = a * bk(y, x) := by simp only [e4u_c]; group
  have S2 : ∀ x ∈ B, ∀ y ∈ B', bk(y, x) ∈ E := by
    intro x hx y hy
    have hcA := S1 x hx y hy
    have hu : bk(bk(y, x), y) ∈ U := hB'G y hy _ hcA
    have hcy : bk(y, x) * y = y * bk(y, x) * bk(bk(y, x), y) := by
      simp only [e4u_c]; group
    have hpow := e4u_pow3 y bk(y, x) bk(bk(y, x), y) hcy (hB'c y hy _ hu)
      (hAab _ hcA _ (hEA (hUE hu)))
    have h1 : (y * bk(y, x)) ^ 3 = 1 := by
      have : y * bk(y, x) = x⁻¹ * y * x⁻¹⁻¹ := by simp only [e4u_c]; group
      rw [this, e4u_conj_pow3, hB'3 y hy]; simp
    rw [h1, hB'3 y hy, hU3 _ hu, one_mul, mul_one] at hpow
    exact hAE _ hcA hpow.symm
  have S3 : ∀ x ∈ B, ∀ y ∈ B', bk(y, x) ∈ U := by
    intro x hx y hy
    by_cases hxU : x ∈ U
    · have : bk(y, x) = 1 := (e4u_c_eq_one_iff y x).mpr (hB'c y hy x hxU)
      rw [this]; exact one_mem U
    · obtain ⟨x', hx', hind⟩ := hpartB x hx hxU
      have hxx' : x * x' = x' * x := hBab x hx x' hx'
      have hd1 := S2 x hx y hy
      have hd2 := S2 x' hx' y hy
      have hmain : bk(y, x') * (bk(y, x) * bk(bk(y, x), x'))
          = bk(y, x) * (bk(y, x') * bk(bk(y, x'), x)) := by
        calc bk(y, x') * (bk(y, x) * bk(bk(y, x), x')) = bk(y, x * x') := by
              simp only [e4u_c]; group
          _ = bk(y, x' * x) := by rw [hxx']
          _ = bk(y, x) * (bk(y, x') * bk(bk(y, x'), x)) := by
              simp only [e4u_c]; group
      have hcomm : bk(y, x') * bk(y, x) = bk(y, x) * bk(y, x') := hEc _ hd2 _ hd1
      have heq : bk(bk(y, x), x') = bk(bk(y, x'), x) := by
        simp only [← mul_assoc] at hmain
        rw [hcomm] at hmain
        exact mul_left_cancel hmain
      exact (e4u_CT E U e hEc hE3 hUE heE hdec hflag x x' (hBc x hx) (hBc x' hx') hind
        _ _ hd1 hd2 heq.symm).1
  have S4 : ∀ x ∈ B, ∀ y ∈ B', (x * y) ^ 3 = 1 := by
    intro x hx y hy
    have ht := S3 x hx y hy
    have hyx : y * x = x * y * bk(y, x) := by simp only [e4u_c]; group
    rw [e4u_pow3 x y bk(y, x) hyx (hBc x hx _ ht) (hB'c y hy _ ht), hB3 x hx, hB'3 y hy,
      hU3 _ ht]
    simp
  have S5 : ∀ y ∈ B', ∃ x ∈ B, ∃ z ∈ E, y = z * x ∧ bk(e, x) = bk(e, y) := by
    intro y hy
    obtain ⟨x, hx, hxe⟩ := hBsurj bk(e, y) (hflag e heE y)
    have hconj : x⁻¹ * e * x = y⁻¹ * e * y := by
      have h2 : e⁻¹ * (x⁻¹ * e * x) = e⁻¹ * (y⁻¹ * e * y) := by
        have := hxe
        simp only [e4u_c] at this
        simpa only [mul_assoc] using this
      exact mul_left_cancel h2
    have hwe : (y * x⁻¹) * e = e * (y * x⁻¹) := by
      calc y * x⁻¹ * e = y * (x⁻¹ * e * x) * x⁻¹ := by group
        _ = y * (y⁻¹ * e * y) * x⁻¹ := by rw [hconj]
        _ = e * (y * x⁻¹) := by group
    have hwU : ∀ u ∈ U, (y * x⁻¹) * u = u * (y * x⁻¹) := fun u hu =>
      (Commute.mul_left (show Commute y u from hB'c y hy u hu)
        (show Commute x u from hBc x hx u hu).inv_left).eq
    have hw3 : (y * x⁻¹) ^ 3 = 1 := by
      have : y * x⁻¹ = x * (x⁻¹ * y) * x⁻¹ := by group
      rw [this, e4u_conj_pow3, S4 x⁻¹ (B.inv_mem hx) y hy]; simp
    have hwE := hI _ (e4u_cent_E E U e hdec _ hwe hwU) hw3
    exact ⟨x, hx, y * x⁻¹, hwE, by group, hxe⟩
  intro y hy
  by_cases hyU : y ∈ U
  · exact hUB hyU
  obtain ⟨y', hy', hind⟩ := hpartB' y hy hyU
  obtain ⟨x, hx, z, hz, hyz, hex⟩ := S5 y hy
  obtain ⟨x', hx', z', hz', hyz', hex'⟩ := S5 y' hy'
  have hind' : ∀ s t : ℕ, bk(e, x) ^ s * bk(e, x') ^ t = 1 → 3 ∣ s ∧ 3 ∣ t := by
    rw [hex, hex']; exact hind
  have hp : bk(z', x) ∈ U := hflag z' hz' x
  have hq : bk(z, x') ∈ U := hflag z hz x'
  have A1 : x * z' = z' * x * bk(z', x)⁻¹ := by simp only [e4u_c]; group
  have A2 : x' * z = z * x' * bk(z, x')⁻¹ := by simp only [e4u_c]; group
  have hpc : bk(z', x)⁻¹ * x' = x' * bk(z', x)⁻¹ :=
    (Commute.inv_right (show Commute x' bk(z', x) from hBc x' hx' _ hp)).eq.symm
  have hqc : bk(z, x')⁻¹ * x = x * bk(z, x')⁻¹ :=
    (Commute.inv_right (show Commute x bk(z, x') from hBc x hx _ hq)).eq.symm
  have hyy : y * y' = z * z' * (x * x') * bk(z', x)⁻¹ := by
    rw [hyz, hyz']
    calc z * x * (z' * x') = z * (x * z') * x' := by group
      _ = z * (z' * x * bk(z', x)⁻¹) * x' := by rw [A1]
      _ = z * z' * x * (bk(z', x)⁻¹ * x') := by group
      _ = z * z' * x * (x' * bk(z', x)⁻¹) := by rw [hpc]
      _ = z * z' * (x * x') * bk(z', x)⁻¹ := by group
  have hyy' : y' * y = z' * z * (x' * x) * bk(z, x')⁻¹ := by
    rw [hyz, hyz']
    calc z' * x' * (z * x) = z' * (x' * z) * x := by group
      _ = z' * (z * x' * bk(z, x')⁻¹) * x := by rw [A2]
      _ = z' * z * x' * (bk(z, x')⁻¹ * x) := by group
      _ = z' * z * x' * (x * bk(z, x')⁻¹) := by rw [hqc]
      _ = z' * z * (x' * x) * bk(z, x')⁻¹ := by group
  have hzz : z * z' = z' * z := hEc z hz z' hz'
  have hxx : x * x' = x' * x := hBab x hx x' hx'
  have hfin := hyy.symm.trans ((hB'ab y hy y' hy').trans hyy')
  rw [← hzz, ← hxx] at hfin
  have hpq : bk(z', x) = bk(z, x') := inv_injective (mul_left_cancel hfin)
  have hCT := e4u_CT E U e hEc hE3 hUE heE hdec hflag x x' (hBc x hx) (hBc x' hx') hind'
    z z' hz hz' hpq
  rw [hyz]
  exact B.mul_mem (hUB hCT.1) hx

theorem e4_uniq {P : Type*} [Group P] (E U A B B' : Subgroup P) (e : P) [A.Normal]
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAcent : ∀ g : P, (∀ a ∈ A, g * a = a * g) → g ∈ A)
    (hEA : E ≤ A) (hAE : ∀ a ∈ A, a ^ 3 = 1 → a ∈ E)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hUE : U ≤ E) (hUcard : Nat.card U = 9)
    (heE : e ∈ E) (_heU : e ∉ U)
    (hdec : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s)
    (hflag : ∀ z ∈ E, ∀ g : P, ⁅z, g⁆ ∈ U)
    (hI : ∀ x : P, (∀ z ∈ E, x * z = z * x) → x ^ 3 = 1 → x ∈ E)
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hBU : B ⊓ E = U)
    (hBsurj : ∀ u ∈ U, ∃ x ∈ B, ⁅e, x⁆ = u)
    (hBG : ∀ x ∈ B, ∀ a ∈ A, ⁅a, x⁆ ∈ U)
    (hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x) (hB'3 : ∀ x ∈ B', x ^ 3 = 1)
    (hB'U : B' ⊓ E = U)
    (hB'surj : ∀ u ∈ U, ∃ x ∈ B', ⁅e, x⁆ = u)
    (hB'G : ∀ x ∈ B', ∀ a ∈ A, ⁅a, x⁆ ∈ U) :
    B' ≤ B := by
  have hflag' : ∀ z ∈ E, ∀ g : P, bk(z, g) ∈ U := fun z hz g => by
    rw [e4u_c_eq_mathlib]; exact hflag _ (E.inv_mem hz) _
  have hsurj : ∀ C : Subgroup P, (∀ u ∈ U, ∃ x ∈ C, ⁅e, x⁆ = u) →
      ∀ u ∈ U, ∃ x ∈ C, bk(e⁻¹, x) = u := fun C h u hu => by
    obtain ⟨x, hx, hxu⟩ := h u hu
    refine ⟨x⁻¹, C.inv_mem hx, ?_⟩
    rw [e4u_c_eq_mathlib, inv_inv, inv_inv]; exact hxu
  have hG : ∀ C : Subgroup P, (∀ x ∈ C, ∀ a ∈ A, ⁅a, x⁆ ∈ U) →
      ∀ x ∈ C, ∀ a ∈ A, bk(a, x) ∈ U := fun C h x hx a ha => by
    rw [e4u_c_eq_mathlib]; exact h _ (C.inv_mem hx) _ (A.inv_mem ha)
  have hdec' : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e⁻¹ ^ s := fun z hz => by
    obtain ⟨v, hv, s, rfl⟩ := hdec z hz
    refine ⟨v, hv, 2 * s, ?_⟩
    congr 1
    have h3 : e ^ s * e ^ (2 * s) = 1 := by
      rw [← pow_add, show s + 2 * s = 3 * s by ring, pow_mul, hE3 e heE, one_pow]
    rw [inv_pow]
    exact eq_inv_of_mul_eq_one_left h3 ▸ rfl
  exact e4u_core E U A B B' e⁻¹ hAab hAcent hEA hAE hE3 hUE hUcard (E.inv_mem heE) hdec'
    hflag' hI hBab hB3 hBU (hsurj B hBsurj) (hG B hBG) hB'ab hB'3 hB'U (hsurj B' hB'surj)
    (hG B' hB'G)


end Uniq

section Main

open Subgroup
open scoped commutatorElement

theorem e4_bridge {P : Type*} [Group P] (hP : IsPGroup 3 P)
    (A U E : Subgroup P) [A.Normal] (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hEA : E ≤ A) (hAE : ∀ a ∈ A, a ^ 3 = 1 → a ∈ E) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hUE : U ≤ E) (e : P) (heE : e ∈ E)
    (hdec : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s)
    (x x' : P) (hx3 : x ^ 3 = 1) (hx'3 : x' ^ 3 = 1) (hxx' : x * x' = x' * x)
    (hxU : ∀ u ∈ U, x * u = u * x) (hx'U : ∀ u ∈ U, x' * u = u * x')
    (hxe : ⁅e, x⁆ ∈ U) (hx'e : ⁅e, x'⁆ ∈ U)
    (hind : ∀ s t : ℕ, ⁅e, x⁆ ^ s * ⁅e, x'⁆ ^ t = 1 → 3 ∣ s ∧ 3 ∣ t) :
    (∀ a ∈ A, ⁅a, x⁆ ∈ U) ∧ (∀ a ∈ A, ⁅a, x'⁆ ∈ U) := by
  classical
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun a b => Subtype.ext (hAab a a.2 b b.2) }
  let c : P → (A →* A) := fun g => (MulAut.conjNormal (H := A) g).toMonoidHom
  have hc : ∀ g (a : A), ((c g a : A) : P) = g * a * g⁻¹ := by
    intro g a
    simp [c]
  have heA : e ∈ A := hEA heE
  let U' : AddSubgroup (Additive A) := (U.subgroupOf A).toAddSubgroup
  have hmemU : ∀ b : A, Additive.ofMul b ∈ U' ↔ (b : P) ∈ U := fun b => Iff.rfl
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := fun u hu => hE3 u (hUE hu)
  have hbr : ∀ (g : P) (a : A), ((c g a * a⁻¹ : A) : P) = ⁅g, (a : P)⁆ := by
    intro g a
    rw [Subgroup.coe_mul, hc, Subgroup.coe_inv, commutatorElement_def]
  let β₁ : Additive A →+ Additive A := (c x).toAdditive
  let β₂ : Additive A →+ Additive A := (c x').toAdditive
  have hsub : ∀ (g : P) (a : A), (c g).toAdditive (Additive.ofMul a) - Additive.ofMul a
      = Additive.ofMul (c g a * a⁻¹) := by
    intro g a
    show Additive.ofMul (c g a) - Additive.ofMul a = _
    rw [← ofMul_div, div_eq_mul_inv]
  have hmem : ∀ (g : P) (a : A), ((c g).toAdditive (Additive.ofMul a) - Additive.ofMul a ∈ U') ↔
      ⁅g, (a : P)⁆ ∈ U := by
    intro g a
    rw [hsub, hmemU, hbr]
  have hc3 : ∀ (g : P), g ^ 3 = 1 → ∀ a : A, c g (c g (c g a)) = a := by
    intro g hg a
    apply Subtype.ext
    rw [hc, hc, hc]
    have h3 : g * g * g = 1 := by simpa [pow_succ, mul_assoc] using hg
    calc g * (g * (g * (a : P) * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * (a : P) * (g * g * g)⁻¹ := by group
      _ = a := by rw [h3]; simp
  have hcc : ∀ a : A, c x (c x' a) = c x' (c x a) := by
    intro a
    apply Subtype.ext
    rw [hc, hc, hc, hc]
    have h1 : x * (x' * (a : P) * x'⁻¹) * x⁻¹ = (x * x') * (a : P) * (x * x')⁻¹ := by group
    have h2 : x' * (x * (a : P) * x⁻¹) * x'⁻¹ = (x' * x) * (a : P) * (x' * x)⁻¹ := by group
    rw [h1, h2, hxx']
  have hUfix : ∀ (g : P), (∀ u ∈ U, g * u = u * g) → ∀ b : A, (b : P) ∈ U → c g b = b := by
    intro g hg b hb
    apply Subtype.ext
    rw [hc, hg _ hb]; group
  have hA3 : ∀ a : Additive A, ∃ k : ℕ, 3 ^ k • a = 0 := by
    intro a
    obtain ⟨k, hk⟩ := hP (a.toMul : P)
    refine ⟨k, ?_⟩
    have : (a.toMul) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    apply Additive.toMul.injective
    simp [toMul_nsmul, this]
  have hU3' : ∀ u ∈ U', 3 • u = 0 := by
    intro u hu
    have hu' : (u.toMul : P) ∈ U := hu
    apply Additive.toMul.injective
    have := hU3 _ hu'
    simp [toMul_nsmul]
    exact Subtype.ext (by simpa using this)
  have hUx : ∀ b : A, Additive.ofMul b ∈ U' → β₁ (Additive.ofMul b) = Additive.ofMul b := by
    intro b hb
    show Additive.ofMul (c x b) = Additive.ofMul b
    rw [hUfix x hxU b hb]
  have hUx' : ∀ b : A, Additive.ofMul b ∈ U' → β₂ (Additive.ofMul b) = Additive.ofMul b := by
    intro b hb
    show Additive.ofMul (c x' b) = Additive.ofMul b
    rw [hUfix x' hx'U b hb]
  let e' : A := ⟨e, heA⟩
  have he3 : (3 : ℕ) • Additive.ofMul e' = 0 := by
    apply Additive.toMul.injective
    simp [toMul_nsmul]
    exact Subtype.ext (by simpa [e'] using hE3 e heE)
  have hEdec : ∀ a : Additive A, (3 : ℕ) • a = 0 → ∃ u ∈ U', ∃ s : ℕ, a = u + s • Additive.ofMul e' := by
    intro a ha
    have h3 : (a.toMul : P) ^ 3 = 1 := by
      have := congrArg Additive.toMul ha
      simp [toMul_nsmul] at this
      simpa using congrArg Subtype.val this
    obtain ⟨v, hv, s, hvs⟩ := hdec _ (hAE _ a.toMul.2 h3)
    refine ⟨Additive.ofMul ⟨v, hEA (hUE hv)⟩, hv, s, ?_⟩
    apply Additive.toMul.injective
    simp [toMul_nsmul, toMul_add]
    exact Subtype.ext (by simpa [e'] using hvs)
  have hNe : ∀ g : P, ⁅e, g⁆ ∈ U → (c g).toAdditive (Additive.ofMul e') - Additive.ofMul e' ∈ U' := by
    intro g hg
    rw [hmem]
    have : ⁅g, e⁆ = ⁅e, g⁆⁻¹ := (commutatorElement_inv e g).symm
    show ⁅g, e⁆ ∈ U
    rw [this]; exact U.inv_mem hg
  have hindA : ∀ s t : ℕ, s • (β₁ (Additive.ofMul e') - Additive.ofMul e') +
      t • (β₂ (Additive.ofMul e') - Additive.ofMul e') = 0 → 3 ∣ s ∧ 3 ∣ t := by
    intro s t hst
    apply hind
    change s • ((c x).toAdditive (Additive.ofMul e') - Additive.ofMul e') +
      t • ((c x').toAdditive (Additive.ofMul e') - Additive.ofMul e') = 0 at hst
    rw [hsub x e', hsub x' e'] at hst
    have h1 := congrArg Additive.toMul hst
    simp only [toMul_add, toMul_nsmul, toMul_ofMul, toMul_zero] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, hbr, Subgroup.coe_one] at h2
    have hxe' : ⁅x, e⁆ ∈ U := by
      rw [← commutatorElement_inv e x]; exact U.inv_mem hxe
    have hx'e' : ⁅x', e⁆ ∈ U := by
      rw [← commutatorElement_inv e x']; exact U.inv_mem hx'e
    have hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := fun u hu v hv => hAab u (hEA (hUE hu)) v (hEA (hUE hv))
    have hcomm' : (⁅x, e⁆ ^ s) * (⁅x', e⁆ ^ t) = (⁅x', e⁆ ^ t) * (⁅x, e⁆ ^ s) :=
      hUc _ (U.pow_mem hxe' s) _ (U.pow_mem hx'e' t)
    have h3 : ⁅e, x⁆ ^ s * ⁅e, x'⁆ ^ t = (⁅x, e⁆ ^ s * ⁅x', e⁆ ^ t)⁻¹ := by
      rw [← commutatorElement_inv x e, ← commutatorElement_inv x' e, inv_pow, inv_pow]
      have hc : Commute (⁅x, e⁆ ^ s) (⁅x', e⁆ ^ t) := hcomm'
      exact ((Commute.inv_inv hc).eq.trans (mul_inv_rev _ _).symm)
    rw [h3, h2]; simp
  have hβ₁c : ∀ a, β₁ (β₂ a) = β₂ (β₁ a) := by
    intro a
    exact congrArg Additive.ofMul (hcc a.toMul)
  have hβ₁3 : ∀ a, β₁ (β₁ (β₁ a)) = a := fun a => congrArg Additive.ofMul (hc3 x hx3 a.toMul)
  have hβ₂3 : ∀ a, β₂ (β₂ (β₂ a)) = a := fun a => congrArg Additive.ofMul (hc3 x' hx'3 a.toMul)
  have key := e4_lemmaM (A := Additive A) hA3 β₁ β₂ hβ₁c hβ₁3 hβ₂3 U' (Additive.ofMul e') hU3'
    (fun u hu => hUx u.toMul hu) (fun u hu => hUx' u.toMul hu) he3 hEdec (hNe x hxe) (hNe x' hx'e) hindA
  have hfin : ∀ (g : P), (∀ a : A, (c g).toAdditive (Additive.ofMul a) - Additive.ofMul a ∈ U') →
      ∀ a ∈ A, ⁅a, g⁆ ∈ U := by
    intro g hg a ha
    have := (hmem g ⟨a, ha⟩).1 (hg ⟨a, ha⟩)
    have h2 : ⁅a, g⁆ = ⁅g, a⁆⁻¹ := (commutatorElement_inv g a).symm
    rw [h2]; exact U.inv_mem this
  exact ⟨hfin x (fun a => (key (Additive.ofMul a)).1), hfin x' (fun a => (key (Additive.ofMul a)).2)⟩



theorem e4_partner {P : Type*} [Group P] (U : Subgroup P) (hUcard : Nat.card U = 9)
    (hU3 : ∀ x ∈ U, x ^ 3 = 1) {u : P} (hu : u ∈ U) (hu1 : u ≠ 1) :
    ∃ v ∈ U, ∀ s t : ℕ, u ^ s * v ^ t = 1 → 3 ∣ s ∧ 3 ∣ t := by
  have hord : orderOf u = 3 := orderOf_eq_prime (hU3 u hu) hu1
  have hcz : Nat.card (Subgroup.zpowers u) = 3 := by rw [Nat.card_zpowers, hord]
  have hfin : Finite U := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨v, hvU, hv⟩ : ∃ v ∈ U, v ∉ Subgroup.zpowers u := by
    by_contra h
    push Not at h
    have h2 : U ≤ Subgroup.zpowers u := h
    have hfin2 : Finite (Subgroup.zpowers u) := Nat.finite_of_card_ne_zero (by omega)
    have := Subgroup.card_le_of_le h2
    omega
  refine ⟨v, hvU, fun s t hst => ?_⟩
  have hv3 : v ^ 3 = 1 := hU3 v hvU
  have ht : 3 ∣ t := by
    by_contra h3
    have h1 : (t % 3 = 1) ∨ (t % 3 = 2) := by omega
    have hvt : v ^ t ∈ Subgroup.zpowers u := by
      have : v ^ t = (u ^ s)⁻¹ := eq_inv_of_mul_eq_one_right hst
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers u) s)
    apply hv
    rcases h1 with h1 | h1
    · have : v = v ^ t := by
        rw [pow_eq_pow_mod t hv3, h1, pow_one]
      rw [this]; exact hvt
    · have : v = (v ^ t) ^ 2 := by
        rw [← pow_mul, pow_eq_pow_mod (t * 2) hv3]
        have : t * 2 % 3 = 1 := by omega
        rw [this, pow_one]
      rw [this]; exact Subgroup.pow_mem _ hvt 2
  obtain ⟨k, hk⟩ := ht
  have hvt1 : v ^ t = 1 := by rw [hk, pow_mul, hv3, one_pow]
  rw [hvt1, mul_one] at hst
  exact ⟨orderOf_dvd_iff_pow_eq_one.2 hst |> fun h => hord ▸ h, ⟨k, hk⟩⟩



theorem e4_exists_normal {P : Type*} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (B₀ : Subgroup P) (hB₀ab : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x) (hB₀3 : ∀ x ∈ B₀, x ^ 3 = 1)
    (hB₀ : Nat.card B₀ = 81) :
    ∃ N : Subgroup P, N.Normal ∧ (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) ∧ (∀ x ∈ N, x ^ 3 = 1) ∧
      Nat.card N = 81 := by
  classical
  by_contra hno
  push Not at hno
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 P) := ⟨hP⟩
  let S : Set (Subgroup P) :=
    {F | F.Normal ∧ (∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ ∀ x ∈ F, x ^ 3 = 1}
  have hSne : S.Nonempty :=
    ⟨⊥, inferInstance, fun x hx y hy => by simp [Subgroup.mem_bot.1 hx, Subgroup.mem_bot.1 hy],
      fun x hx => by simp [Subgroup.mem_bot.1 hx]⟩
  obtain ⟨E, hES, hEmax⟩ := Set.exists_max_image S (fun F => Nat.card F) (Set.toFinite S) hSne
  obtain ⟨hEn, hEab, hE3⟩ := hES
  have : E.Normal := hEn
  have hEcard : Nat.card E ≤ 27 := by
    by_contra h
    push Not at h
    obtain ⟨k, hk⟩ := (hP.to_subgroup E).exists_card_eq
    have hk4 : 4 ≤ k := by
      by_contra hk4
      push Not at hk4
      have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨K, hKn, hKE, hKcard⟩ :=
      CFSG.exists_normal_subgroup_card_pow_of_normal E hEn hk 4 hk4
    exact hno K hKn (fun x hx y hy => hEab x (hKE hx) y (hKE hy)) (fun x hx => hE3 x (hKE hx))
      (by rw [hKcard]; norm_num)
  have hI : ∀ x : P, (∀ e ∈ E, x * e = e * x) → x ^ 3 = 1 → x ∈ E := by
    have hEel : CFSG.IsElementaryAbelian 3 E :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2
        ⟨⟨⟨fun a b => Subtype.ext (hEab a a.2 b b.2)⟩⟩, hE3⟩
    have hmax : ∀ B : Subgroup P, B.Normal → CFSG.IsElementaryAbelian 3 B → E ≤ B → B = E := by
      intro B hBn hBel hEB
      obtain ⟨hBc, hBp⟩ := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 B).1 hBel
      have hBS : B ∈ S :=
        ⟨hBn, fun x hx y hy => congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : B) ⟨y, hy⟩), hBp⟩
      exact (Subgroup.eq_of_le_of_card_ge hEB (hEmax B hBS)).symm
    intro x hx hx3
    exact (CFSG.RankThree.PGroups.maximal_normal_elementary_centralizer_torsion
      Nat.prime_three (by norm_num) hP hEel hmax).2 x
      (mem_centralizer_iff.2 fun h hh => (hx h hh).symm) hx3
  obtain ⟨hE27, U, hUn, hUE, hUcard, hflag, hcls⟩ :=
    e4_classify hP E hEab hE3 hEcard hI B₀ hB₀ab hB₀3 hB₀
  have : U.Normal := hUn
  obtain ⟨e, heE, heU⟩ : ∃ e ∈ E, e ∉ U := by
    by_contra h
    push Not at h
    have h2 : E ≤ U := h
    have := Subgroup.card_le_of_le h2
    omega
  have hdec : ∀ z ∈ E, ∃ v ∈ U, ∃ s : ℕ, z = v * e ^ s :=
    e4_decomp hEab hUE (by rw [hE27, hUcard]) heE heU
  let S2 : Set (Subgroup P) :=
    {A | A.Normal ∧ E ≤ A ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}
  have hS2ne : S2.Nonempty := ⟨E, hEn, le_rfl, hEab⟩
  obtain ⟨A, hAmax⟩ := (Set.toFinite S2).exists_maximal hS2ne
  obtain ⟨hAn, hEA, hAab⟩ := hAmax.1
  have : A.Normal := hAn
  have hAmax' : ∀ B : Subgroup P, B.Normal → (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B →
      B = A := by
    intro B hBn hBab hAB
    exact le_antisymm (hAmax.2 ⟨hBn, hEA.trans hAB, hBab⟩ hAB) hAB
  have hAc : centralizer (A : Set P) = A :=
    CFSG.SectionRank.Ccomm.maximal_abelian_normal_self_centralizing hP hAab hAmax'
  have hAcent : ∀ g : P, (∀ a ∈ A, g * a = a * g) → g ∈ A := by
    intro g hg
    rw [← hAc]
    exact mem_centralizer_iff.2 fun h hh => (hg h hh).symm
  have hAE : ∀ a ∈ A, a ^ 3 = 1 → a ∈ E := by
    let T : Subgroup P :=
      { carrier := {x | x ∈ A ∧ x ^ 3 = 1}
        mul_mem' := by
          rintro a b ⟨haA, ha3⟩ ⟨hbA, hb3⟩
          refine ⟨A.mul_mem haA hbA, ?_⟩
          rw [(show Commute a b from hAab a haA b hbA).mul_pow, ha3, hb3, one_mul]
        one_mem' := ⟨A.one_mem, one_pow 3⟩
        inv_mem' := by
          rintro a ⟨haA, ha3⟩
          exact ⟨A.inv_mem haA, by rw [inv_pow, ha3, inv_one]⟩ }
    have hTn : T.Normal := by
      refine ⟨fun n hn g => ⟨hAn.conj_mem n hn.1 g, ?_⟩⟩
      rw [conj_pow, hn.2]; simp
    have hTS : T ∈ S :=
      ⟨hTn, fun x hx y hy => hAab x hx.1 y hy.1, fun x hx => hx.2⟩
    have hET : E ≤ T := fun x hx => ⟨hEA hx, hE3 x hx⟩
    have hTE : T = E := (Subgroup.eq_of_le_of_card_ge hET (hEmax T hTS)).symm
    intro a ha ha3
    have : a ∈ T := ⟨ha, ha3⟩
    rwa [hTE] at this
  have hBG : ∀ B : Subgroup P, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x ^ 3 = 1) →
      Nat.card B = 81 → ∀ x ∈ B, ∀ a ∈ A, ⁅a, x⁆ ∈ U := by
    intro B hBab hB3 hBc x hx a ha
    obtain ⟨hBU, hBsurj⟩ := hcls B hBab hB3 hBc
    have hUB : U ≤ B := hBU ▸ inf_le_left
    have hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u :=
      fun u hu v hv => hEab u (hUE hu) v (hUE hv)
    have hU3 : ∀ u ∈ U, u ^ 3 = 1 := fun u hu => hE3 u (hUE hu)
    have hcentU : ∀ y ∈ B, ∀ u ∈ U, y * u = u * y := fun y hy u hu => hBab y hy u (hUB hu)
    by_cases hxU : x ∈ U
    · have h1 : ⁅a, x⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact hAab a ha x (hEA (hUE hxU))
      rw [h1]; exact U.one_mem
    ·
      have hex : ⁅e, x⁆ ≠ 1 := by
        intro h1
        rw [commutatorElement_eq_one_iff_mul_comm] at h1
        apply hxU
        have hxE : x ∈ E := by
          apply hI x _ (hB3 x hx)
          intro z hz
          obtain ⟨v, hv, s, rfl⟩ := hdec z hz
          have h2 : x * v = v * x := hcentU x hx v hv
          have h3 : x * e ^ s = e ^ s * x := by
            have hc : Commute x e := h1.symm
            exact (hc.pow_right s).eq
          calc x * (v * e ^ s) = (x * v) * e ^ s := by rw [mul_assoc]
            _ = (v * x) * e ^ s := by rw [h2]
            _ = v * (x * e ^ s) := by rw [mul_assoc]
            _ = v * (e ^ s * x) := by rw [h3]
            _ = (v * e ^ s) * x := by rw [mul_assoc]
        have : x ∈ B ⊓ E := ⟨hx, hxE⟩
        rwa [hBU] at this
      obtain ⟨v, hvU, hv⟩ := e4_partner U hUcard hU3 (hflag e heE x) hex
      obtain ⟨x', hx', hx'v⟩ := hBsurj e heE heU v hvU
      have hbr := e4_bridge hP A U E hAab hEA hAE hE3 hUE e heE hdec x x' (hB3 x hx) (hB3 x' hx')
        (hBab x hx x' hx') (hcentU x hx) (hcentU x' hx') (hflag e heE x) (hflag e heE x')
        (by rw [hx'v]; exact hv)
      exact hbr.1 a ha
  have hnorm : B₀.Normal := by
    refine ⟨fun n hn g => ?_⟩
    let B' : Subgroup P := B₀.map (MulAut.conj g).toMonoidHom
    have hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, hB₀ab x hx y hy]
    have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, hB₀3 x hx, map_one]
    have hB'c : Nat.card B' = 81 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hB₀
    obtain ⟨hBU0, hBsurj0⟩ := hcls B₀ hB₀ab hB₀3 hB₀
    obtain ⟨hBU1, hBsurj1⟩ := hcls B' hB'ab hB'3 hB'c
    have hle : B' ≤ B₀ :=
      e4_uniq E U A B₀ B' e hAab hAcent hEA hAE hE3 hUE hUcard heE heU hdec hflag hI hB₀ab hB₀3
        hBU0 (hBsurj0 e heE heU) (hBG B₀ hB₀ab hB₀3 hB₀) hB'ab hB'3 hBU1 (hBsurj1 e heE heU)
        (hBG B' hB'ab hB'3 hB'c)
    exact hle ⟨n, hn, rfl⟩
  exact hno B₀ hnorm hB₀ab hB₀3 hB₀



theorem gl83NormalElementaryRankFour_holds :
    CFSG.LocalAnalysis.RankFourTheoremC.GL83NormalElementaryRankFour := by
  intro G _ _ P hP h4
  classical
  have hP' : IsPGroup 3 P := hP
  let S : Set ℕ := {k | ∃ E : Subgroup G, E ≤ P ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}
  have hne : S.Nonempty :=
    ⟨0, ⊥, bot_le, ⟨inferInstance, fun x hx => by simp [Subgroup.mem_bot.1 hx]⟩, by simp⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card G, ?_⟩
    rintro k ⟨E, -, -, hE⟩
    have h1 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
    omega
  have hmem := Nat.sSup_mem hne hbdd
  have h4' : 4 ≤ sSup S := h4
  obtain ⟨E, hEP, ⟨hEc, hE3⟩, hEcard⟩ := hmem
  have hk4 : 4 ≤ sSup S := h4'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := 4)
    (by rw [hEcard]; exact pow_dvd_pow 3 hk4)
  let B₀ : Subgroup G := K.map E.subtype
  have hB₀E : B₀ ≤ E := by
    rintro _ ⟨x, -, rfl⟩; exact x.2
  have hB₀ab : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm' (⟨x, hB₀E hx⟩ : E) ⟨y, hB₀E hy⟩)
  have hB₀3 : ∀ x ∈ B₀, x ^ 3 = 1 := fun x hx => hE3 x (hB₀E hx)
  have hB₀card : Nat.card B₀ = 81 := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hK]; norm_num
  have hB₀P : B₀ ≤ P := hB₀E.trans hEP
  have hPfin : Finite P := inferInstance
  let B₁ : Subgroup P := B₀.subgroupOf P
  have hB₁card : Nat.card B₁ = 81 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀P).toEquiv, hB₀card]
  have hB₁ab : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x := by
    intro x hx y hy
    exact Subtype.ext (hB₀ab _ hx _ hy)
  have hB₁3 : ∀ x ∈ B₁, x ^ 3 = 1 := by
    intro x hx
    exact Subtype.ext (hB₀3 _ hx)
  obtain ⟨N, hNn, hNab, hN3, hNcard⟩ := e4_exists_normal hP' B₁ hB₁ab hB₁3 hB₁card
  refine ⟨N.map P.subtype, ?_, ?_, ⟨⟨⟨?_⟩⟩, ?_⟩, ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact x.2
  · rw [le_normalizer_iff]
    rintro s hs _ ⟨x, hx, rfl⟩
    exact ⟨⟨s, hs⟩ * x * ⟨s, hs⟩⁻¹, hNn.conj_mem x hx ⟨s, hs⟩, rfl⟩
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    apply Subtype.ext
    show P.subtype x * P.subtype y = P.subtype y * P.subtype x
    rw [← map_mul, ← map_mul, hNab x hx y hy]
  · rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hN3 x hx)
  · rw [Subgroup.card_map_of_injective P.subtype_injective, hNcard]; norm_num

end Main

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
