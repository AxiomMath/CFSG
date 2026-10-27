module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB.Std

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

variable {G : Type} [Group G] [Finite G]

@[expose] def eSet (Ω : Set (Subgroup G)) (z : G) (M : Subgroup G) : Set G :=
  {t | (∃ g : G, g * z * g⁻¹ = t) ∧ ∃ L ∈ twinSet Ω M, ∃ L' ∈ twinSet Ω M, t ∈ L ⊔ L'}

@[expose] def eGrp (Ω : Set (Subgroup G)) (z : G) (M : Subgroup G) : Subgroup G :=
  Subgroup.closure (eSet Ω z M)

@[expose] def conjGrp (z : G) : Subgroup G :=
  Subgroup.closure {t | ∃ g : G, g * z * g⁻¹ = t}

theorem eGrp_le_conjGrp (Ω : Set (Subgroup G)) (z : G) (M : Subgroup G) :
    eGrp Ω z M ≤ conjGrp z :=
  Subgroup.closure_mono fun _ ht => ht.1

private theorem closure_comm_of_comm {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) :
    ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S :=
    (Subgroup.closure_le _).mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      hS b hb a ha
  intro a ha b hb
  have h2 : S ⊆ Subgroup.centralizer ({a} : Set G) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (h1 ha) s hs)
  have h3 := (Subgroup.closure_le _).mpr h2 hb
  exact (Subgroup.mem_centralizer_singleton_iff.mp h3).symm

private theorem closure_sq_of_comm {S : Set G} (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hS2 : ∀ a ∈ S, a * a = 1) : ∀ x ∈ Subgroup.closure S, x * x = 1 := by
  have hc := closure_comm_of_comm hS
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS2 x hx
  | one => exact mul_one 1
  | mul x y hx hy h1 h2 =>
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [hc y hy x hx]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [h1, h2, mul_one]
  | inv x _ h =>
    rw [← mul_inv_rev, h, inv_one]

theorem eGrp_eq_of_twin {Ω : Set (Subgroup G)} (z : G) {M N : Subgroup G}
    (hN : N ∈ twinSet Ω M) : eGrp Ω z N = eGrp Ω z M := by
  unfold eGrp eSet
  rw [twinSet_eq_twinSet_of_mem hN]

theorem eGrp_conjSub {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (z g : G) (M : Subgroup G) :
    eGrp Ω z (conjSub g M) = conjSub g (eGrp Ω z M) := by
  have hgen : ∀ (g : G) (M : Subgroup G), ∀ t ∈ eSet Ω z M,
      g * t * g⁻¹ ∈ eSet Ω z (conjSub g M) := by
    intro g M t ⟨⟨h, hh⟩, L, hL, L', hL', htL⟩
    refine ⟨⟨g * h, by rw [← hh]; group⟩, conjSub g L, ?_, conjSub g L', ?_, ?_⟩
    · rw [twinSet_conjSub hΩ]
      exact ⟨L, hL, rfl⟩
    · rw [twinSet_conjSub hΩ]
      exact ⟨L', hL', rfl⟩
    · rw [← Sec7.conjSub_sup_eq]
      exact conj_mem_conjSub htL
  have hle : ∀ (g : G) (M : Subgroup G), conjSub g (eGrp Ω z M) ≤ eGrp Ω z (conjSub g M) := by
    intro g M
    change Subgroup.map (MulAut.conj g).toMonoidHom (eGrp Ω z M) ≤ _
    rw [Subgroup.map_le_iff_le_comap]
    refine (Subgroup.closure_le _).mpr fun t ht => ?_
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    exact Subgroup.subset_closure (by simpa using hgen g M t ht)
  refine le_antisymm ?_ (hle g M)
  have h1 := hle g⁻¹ (conjSub g M)
  rw [conjSub_inv_conjSub] at h1
  have h2 := conjSub_mono (n := g) h1
  rwa [conjSub_conjSub_inv] at h2

namespace Std

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {z j : G} (h : Std Ω K J z j)
include h

theorem conjGrp_comm : ∀ a ∈ conjGrp z, ∀ b ∈ conjGrp z, a * b = b * a :=
  closure_comm_of_comm fun _ ⟨g, hg⟩ _ ⟨g', hg'⟩ => hg ▸ hg' ▸ h.conj_comm' g g'

theorem conjGrp_sq : ∀ x ∈ conjGrp z, x * x = 1 :=
  closure_sq_of_comm (fun _ ⟨g, hg⟩ _ ⟨g', hg'⟩ => hg ▸ hg' ▸ h.conj_comm' g g')
    fun _ ⟨g, hg⟩ => by
      rw [← hg]
      calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
        _ = 1 := by rw [h.hz.sq]; group

theorem eGrp_comm (M : Subgroup G) : ∀ a ∈ eGrp Ω z M, ∀ b ∈ eGrp Ω z M, a * b = b * a :=
  fun a ha b hb => h.conjGrp_comm a (eGrp_le_conjGrp Ω z M ha) b (eGrp_le_conjGrp Ω z M hb)

theorem eGrp_sq (M : Subgroup G) : ∀ x ∈ eGrp Ω z M, x * x = 1 :=
  fun x hx => h.conjGrp_sq x (eGrp_le_conjGrp Ω z M hx)

theorem mem_eGrp_self {M : Subgroup G} (hM : M ∈ Ω) {m : G} (hm : IsUniqueInvolution M m) :
    m ∈ eGrp Ω z M :=
  Subgroup.subset_closure ⟨h.exists_conj hM hm, M, ⟨hM, m, hm, hm⟩, M, ⟨hM, m, hm, hm⟩,
    Subgroup.mem_sup_left hm.mem⟩

theorem exists_conjSub {M : Subgroup G} (hM : M ∈ Ω) :
    ∃ g : G, conjSub g⁻¹ M ∈ twinSet Ω K := by
  obtain ⟨m, hm⟩ := Sec6Gen.exists_uniqueInvolution h.hΩ.hyp hM
  obtain ⟨g, hg⟩ := h.exists_conj hM hm
  refine ⟨g, h.hΩ.hyp.conjInvariant g⁻¹ M hM, z, h.hz, ?_⟩
  have h1 := hm.conj g⁻¹
  rwa [← hg, show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h1

theorem exists_eGrp_eq {M : Subgroup G} (hM : M ∈ Ω) :
    ∃ g : G, eGrp Ω z M = conjSub g (eGrp Ω z K) := by
  obtain ⟨g, hg⟩ := h.exists_conjSub hM
  refine ⟨g, ?_⟩
  rw [← eGrp_eq_of_twin z hg, ← eGrp_conjSub h.hΩ.hyp.conjInvariant, conjSub_conjSub_inv]

theorem card_eGrp {M : Subgroup G} (hM : M ∈ Ω) :
    Nat.card (eGrp Ω z M) = Nat.card (eGrp Ω z K) := by
  obtain ⟨g, hg⟩ := h.exists_eGrp_eq hM
  rw [hg, AscL62.natCard_conjSub]

section Pair

variable {M N M' : Subgroup G} {m n u v : G}

theorem eGrp_le_Y (d : LJ Ω M N M' m n u v) : eGrp Ω z M ≤ pairNormalizers M N m n := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro t ⟨-, L, hL, L', hL', htL⟩
  have hle : ∀ L₀ ∈ twinSet Ω M, L₀ ≤ pairNormalizers M N m n := by
    intro L₀ hL₀
    rw [d.tor.htw] at hL₀
    rcases hL₀ with rfl | rfl
    · exact d.K_le_Y
    · exact d.K'_le_Y
  exact sup_le (hle L hL) (hle L' hL') htL

theorem eGrp_le_Y' (d : LJ Ω M N M' m n u v) : eGrp Ω z N ≤ pairNormalizers M N m n := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro t ⟨-, L, hL, L', hL', htL⟩
  exact sup_le (d.twin_J.1 L hL) (d.twin_J.1 L' hL') htL

theorem mem_eGrp_of_LJ (d : LJ Ω M N M' m n u v) : n ∈ eGrp Ω z M := by
  have hM'tw : M' ∈ twinSet Ω M := by
    rw [d.tor.htw]
    exact Or.inr rfl
  exact Subgroup.subset_closure ⟨h.exists_conj d.tor.hJ d.tor.hj, M, ⟨d.tor.hK, m, d.tor.hz,
    d.tor.hz⟩, M', hM'tw, d.j_mem_KK'⟩

theorem le_centralizer_Z (d : LJ Ω M N M' m n u v) {B : Subgroup G} (hB : B ≤ conjGrp z)
    (hmB : m ∈ B) (hnB : n ∈ B) :
    B ≤ Subgroup.centralizer ((Subgroup.closure ({m, n} : Set G) : Subgroup G) : Set G) :=
  fun x hx => d.tor.mem_C_Z_of_comm (h.conjGrp_comm x (hB hx) m (hB hmB))
    (h.conjGrp_comm x (hB hx) n (hB hnB))

theorem card_le_four_of_le_UV (d : LJ Ω M N M' m n u v) {B : Subgroup G}
    (hB2 : ∀ x ∈ B, x * x = 1) (hBX : B ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v) :
    Nat.card B ≤ 4 := by
  have hle : B ≤ (Subgroup.closure ({m, n} : Set G) : Subgroup G) :=
    fun x hx => d.tor.mem_Z_of_sq (hBX hx) (hB2 x hx)
  have := Subgroup.card_le_of_le hle
  rw [d.card_Z] at this
  exact this

theorem eGrp_eq_of_aViol (h8 : Nat.card (eGrp Ω z K) = 8) (hM : M ∈ Ω) (hv : AViol Ω M N m n) :
    eGrp Ω z M = eGrp Ω z N := by
  obtain ⟨M', u, v, d⟩ := exists_LJ h.hΩ hM hv.mem (WR1.inA_of_aViol hv) hv.hzK hv.hzJ
    (fun L hL => h.isPGroup hL)
  have hM8 : Nat.card (eGrp Ω z M) = 8 := (h.card_eGrp hM).trans h8
  have hN8 : Nat.card (eGrp Ω z N) = 8 := (h.card_eGrp hv.mem).trans h8
  set B := eGrp Ω z M ⊔ eGrp Ω z N with hB
  have hBc : B ≤ conjGrp z := sup_le (eGrp_le_conjGrp Ω z M) (eGrp_le_conjGrp Ω z N)
  have hmB : m ∈ B := Subgroup.mem_sup_left (h.mem_eGrp_self hM hv.hzK)
  have hnB : n ∈ B := Subgroup.mem_sup_left (h.mem_eGrp_of_LJ d)
  have hBY : B ≤ pairNormalizers M N m n := sup_le (h.eGrp_le_Y d) (h.eGrp_le_Y' d)
  have hBX : ¬ B ≤ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
    intro hle
    have := h.card_le_four_of_le_UV d (fun x hx => h.conjGrp_sq x (eGrp_le_conjGrp Ω z M hx))
      (le_sup_left.trans hle)
    omega
  have h8B := d.card_le_eight hBY (h.le_centralizer_Z d hBc hmB hnB)
    (fun a ha b hb => h.conjGrp_comm a (hBc ha) b (hBc hb)) hBX
  have e1 : eGrp Ω z M = B := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
  have e2 : eGrp Ω z N = B := Subgroup.eq_of_le_of_card_ge le_sup_right (by omega)
  rw [e1, e2]

end Pair

theorem eGrp_eq (h8 : Nat.card (eGrp Ω z K) = 8) {M : Subgroup G} (hM : M ∈ Ω) :
    eGrp Ω z M = eGrp Ω z K := by
  have hMA : M ∈ aStar Ω K := h.hall.symm ▸ hM
  induction hMA with
  | refl => rfl
  | tail hab hbc ih =>
    rename_i b c
    have hb : b ∈ Ω := by
      rcases Relation.ReflTransGen.cases_tail hab with rfl | ⟨_, _, hb⟩
      · exact h.hK
      · exact hb.1
    rw [← ih hb]
    obtain ⟨hcΩ, ⟨zb, zc, hvbc⟩ | ⟨zc, zb, hvcb⟩ | ⟨htw, -⟩⟩ := hbc
    · exact (h.eGrp_eq_of_aViol h8 hb hvbc).symm
    · exact h.eGrp_eq_of_aViol h8 hcΩ hvcb
    · exact eGrp_eq_of_twin z htw

theorem conj_mem_eGrp (h8 : Nat.card (eGrp Ω z K) = 8) (g : G) :
    g * z * g⁻¹ ∈ eGrp Ω z K := by
  have hKg := h.hΩ.hyp.conjInvariant g K h.hK
  rw [← h.eGrp_eq h8 hKg]
  exact h.mem_eGrp_self hKg (h.hz.conj g)

theorem eGrp_normal (h8 : Nat.card (eGrp Ω z K) = 8) : (eGrp Ω z K).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hKg := h.hΩ.hyp.conjInvariant g K h.hK
  have h1 : g * x * g⁻¹ ∈ conjSub g (eGrp Ω z K) := conj_mem_conjSub hx
  rwa [← eGrp_conjSub h.hΩ.hyp.conjInvariant, h.eGrp_eq h8 hKg] at h1

section KJ

variable {K' : Subgroup G} {u v s : G}

theorem sq_eq_one_of_comm (d : LJ Ω K J K' z j u v) {c x : G} (hcY : c ∈ pairNormalizers K J z j)
    (hcZ : c ∈ Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G))
    (hc : c ∉ Subgroup.zpowers u ⊔ Subgroup.zpowers v)
    (hx : x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v) (hxc : x * c = c * x) : x * x = 1 := by
  have h1 := (d.inv_of_not_mem hcY hcZ hc).1 x hx
  have h2 : c * x * c⁻¹ = x := by rw [← hxc]; group
  rw [h2] at h1
  calc x * x = x * x⁻¹ := by rw [← h1]
    _ = 1 := mul_inv_cancel x

theorem eGrp_facts (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) :
    eGrp Ω z K ≤ pairNormalizers K J z j ⊓
      Subgroup.centralizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) ∧
    s ∈ eGrp Ω z K ∧ s ∉ Subgroup.zpowers u ⊔ Subgroup.zpowers v := by
  obtain ⟨hsz, ⟨L, hL, hsL⟩, hsZ⟩ := hs
  have hsE : s ∈ eGrp Ω z K := Subgroup.subset_closure ⟨hsz, L, hL, K, ⟨h.hK, z, h.hz, h.hz⟩, hsL⟩
  refine ⟨le_inf (h.eGrp_le_Y d) (h.le_centralizer_Z d (eGrp_le_conjGrp Ω z K)
    (h.mem_eGrp_self h.hK h.hz) (h.mem_eGrp_of_LJ d)), hsE, fun hsX => hsZ ?_⟩
  exact d.tor.mem_Z_of_sq hsX (h.eGrp_sq K s hsE)

theorem mem_eGrp_cases (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) {e : G} (he : e ∈ eGrp Ω z K) :
    e ∈ Subgroup.closure ({z, j} : Set G) ∨ s⁻¹ * e ∈ Subgroup.closure ({z, j} : Set G) := by
  obtain ⟨hEle, hsE, hsX⟩ := h.eGrp_facts d hs
  have hsY := (hEle hsE).1
  have hsC := (hEle hsE).2
  have hin : ∀ x ∈ eGrp Ω z K, x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v →
      x ∈ Subgroup.closure ({z, j} : Set G) := fun x hx hxX =>
    d.tor.mem_Z_of_sq hxX (h.sq_eq_one_of_comm d hsY hsC hsX hxX (h.eGrp_comm K x hx s hsE))
  by_cases heX : e ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v
  · exact Or.inl (hin e he heX)
  · exact Or.inr (hin _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hsE) he)
      (d.inv_mul_mem_of_not_mem hsY hsC hsX (hEle he).1 (hEle he).2 heX))

theorem card_eGrp_K (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) :
    Nat.card (eGrp Ω z K) = 8 := by
  obtain ⟨hEle, hsE, hsX⟩ := h.eGrp_facts d hs
  have h8 := d.card_le_eight (hEle.trans inf_le_left) (hEle.trans inf_le_right)
    (h.eGrp_comm K) (fun hle => hsX (hle hsE))
  have hZE : (Subgroup.closure ({z, j} : Set G) : Subgroup G) ≤ eGrp Ω z K := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact h.mem_eGrp_self h.hK h.hz
    · exact h.mem_eGrp_of_LJ d
  have hdvd := Subgroup.card_dvd_of_le hZE
  rw [d.card_Z] at hdvd
  have hne : Nat.card (eGrp Ω z K) ≠ 4 := by
    intro h4
    have heq := Subgroup.eq_of_le_of_card_ge hZE (by rw [h4, d.card_Z])
    exact hs.2.2 (heq ▸ hsE)
  have hpos : 0 < Nat.card (eGrp Ω z K) := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : k ≤ 2 := by omega
  interval_cases k <;> omega

theorem le_eGrp_of_centralizer (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) :
    pairNormalizers K J z j ⊓ Subgroup.centralizer (eGrp Ω z K : Set G) ≤ eGrp Ω z K := by
  obtain ⟨hEle, hsE, hsX⟩ := h.eGrp_facts d hs
  have hsY := (hEle hsE).1
  have hsC := (hEle hsE).2
  have hZE : (Subgroup.closure ({z, j} : Set G) : Subgroup G) ≤ eGrp Ω z K := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact h.mem_eGrp_self h.hK h.hz
    · exact h.mem_eGrp_of_LJ d
  rintro c ⟨hcY, hcE⟩
  have hcs : c * s = s * c := (Subgroup.mem_centralizer_iff.mp hcE s hsE).symm
  have hcZ : c ∈ Subgroup.centralizer
      ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => Subgroup.mem_centralizer_iff.mp hcE x (hZE hx)
  by_cases hcX : c ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v
  · exact hZE (d.tor.mem_Z_of_sq hcX (h.sq_eq_one_of_comm d hsY hsC hsX hcX hcs))
  · have hw := d.inv_mul_mem_of_not_mem hsY hsC hsX hcY hcZ hcX
    have hws : s⁻¹ * c * s = s * (s⁻¹ * c) := by
      calc s⁻¹ * c * s = s⁻¹ * (c * s) := by group
        _ = s⁻¹ * (s * c) := by rw [hcs]
        _ = s * (s⁻¹ * c) := by group
    have hwZ := hZE (d.tor.mem_Z_of_sq hw (h.sq_eq_one_of_comm d hsY hsC hsX hw hws))
    have : c = s * (s⁻¹ * c) := by group
    rw [this]
    exact Subgroup.mul_mem _ hsE hwZ

theorem exists_conj_of_mem_eGrp (d : LJ Ω K J K' z j u v)
    (hs : (∃ g : G, g * z * g⁻¹ = s) ∧ (∃ L ∈ twinSet Ω K, s ∈ L ⊔ K) ∧
      s ∉ Subgroup.closure ({z, j} : Set G)) {e : G} (he : e ∈ eGrp Ω z K) (he1 : e ≠ 1) :
    ∃ g : G, g * z * g⁻¹ = e := by
  obtain ⟨hEle, hsE, hsX⟩ := h.eGrp_facts d hs
  have hsY := (hEle hsE).1
  have hsC := (hEle hsE).2
  have hZ : ∀ w ∈ Subgroup.closure ({z, j} : Set G), w ≠ 1 → ∃ g : G, g * z * g⁻¹ = w := by
    intro w hw hw1
    rcases d.mem_Z_cases hw with h1 | h1
    · exact absurd h1 hw1
    · obtain ⟨y, -, hy⟩ := d.exists_conj_z h1
      exact ⟨y⁻¹, by rw [← hy]; group⟩
  rcases h.mem_eGrp_cases d hs he with heZ | heZ
  · exact hZ e heZ he1
  · obtain ⟨g, hg⟩ := hs.1
    set w := s⁻¹ * e with hw
    have hwE : w ∈ eGrp Ω z K := Subgroup.mul_mem _ (Subgroup.inv_mem _ hsE) he
    have he' : e = w * s := by
      rw [← h.eGrp_comm K s hsE _ hwE, hw]
      group
    have huv : u * v = v * u := d.tor.hcomm u (Subgroup.mem_zpowers u) v (Subgroup.mem_zpowers v)
    obtain ⟨x, hxX, hxx⟩ : ∃ x ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v, x * x = w := by
      rcases d.mem_Z_cases heZ with h1 | h1 | h1 | h1
      · exact ⟨1, Subgroup.one_mem _, by rw [h1, mul_one]⟩
      · exact ⟨u, Subgroup.mem_sup_left (Subgroup.mem_zpowers u), by rw [h1, d.u_sq]⟩
      · exact ⟨v, Subgroup.mem_sup_right (Subgroup.mem_zpowers v), by rw [h1, d.v_sq]⟩
      · refine ⟨u * v, Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers v)), ?_⟩
        rw [h1, ← d.u_sq, ← d.v_sq]
        calc u * v * (u * v) = u * (v * u) * v := by group
          _ = u * (u * v) * v := by rw [huv]
          _ = u * u * (v * v) := by group
    refine ⟨x * g, ?_⟩
    have hxs := d.conj_of_not_mem hsY hsC hsX hxX
    calc x * g * z * (x * g)⁻¹ = x * (g * z * g⁻¹) * x⁻¹ := by group
      _ = x * s * x⁻¹ := by rw [hg]
      _ = e := by rw [hxs, hxx, he']

end KJ

end Std

end CFSG.ClassicalInvolution.Q3.PhilipHall.Thm3Step.ThmB
