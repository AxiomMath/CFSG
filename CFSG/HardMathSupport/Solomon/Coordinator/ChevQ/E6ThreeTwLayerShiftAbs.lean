module

public import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open scoped commutatorElement

section Quasi

theorem shiftQs_exists_noncomm {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, a, b, hab⟩ := h
  apply hab
  induction a using QuotientGroup.induction_on with | H a => ?_
  induction b using QuotientGroup.induction_on with | H b => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcon a b]

theorem shiftQs_normal_dichotomy {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q)
    (M : Subgroup Q) [M.Normal] : M ≤ Subgroup.center Q ∨ M = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := h
  rcases hsimple.eq_bot_or_eq_top_of_normal
    (M.map (QuotientGroup.mk' (Subgroup.center Q))) with h0 | h1
  · left
    intro x hx
    have : QuotientGroup.mk' (Subgroup.center Q) x ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) :=
      h0 ▸ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp this)
  · right
    have hMZ : M ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) M
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : _root_.commutator Q ≤ M := by
      have e : _root_.commutator Q = ⁅M ⊔ Subgroup.center Q, M ⊔ Subgroup.center Q⁆ := by
        rw [hMZ]; rfl
      rw [e]
      have hn : (M ⊔ Subgroup.center Q).Normal := by rw [hMZ]; infer_instance
      rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq,
        Subgroup.commutator_sup_left, Subgroup.commutator_center_right, sup_bot_eq]
      exact Subgroup.commutator_le_left M M
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle

variable {W : Type*} [Group W]

theorem shiftQs_commutator_self {N : Subgroup W} (hN : CFSG.IsQuasisimple N) : ⁅N, N⁆ = N := by
  have h := congrArg (Subgroup.map N.subtype) hN.1.commutator_eq_top
  have e2 : Subgroup.map N.subtype (⊤ : Subgroup ↥N) = N := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have e1 : Subgroup.map N.subtype (_root_.commutator ↥N) = ⁅N, N⁆ := by
    have : _root_.commutator ↥N = ⁅(⊤ : Subgroup ↥N), ⊤⁆ := rfl
    rw [this, Subgroup.map_commutator, e2]
  rw [e1, e2] at h
  exact h

theorem shiftComm_inf_central {Kb A B : Subgroup W}
    (hAK : A ≤ Kb) (hBK : B ≤ Kb) (hAn : Kb ≤ Subgroup.normalizer (A : Set W))
    (hBn : Kb ≤ Subgroup.normalizer (B : Set W)) (hAq : CFSG.IsQuasisimple ↥A)
    (hBq : CFSG.IsQuasisimple ↥B) (hne : A ≠ B) : ∀ x ∈ A ⊓ B, ∀ a ∈ A, a * x = x * a := by
  have hM : ((A ⊓ B).subgroupOf A).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hx' : (x : W) ∈ A ⊓ B := hx
    show ((g * x * g⁻¹ : ↥A) : W) ∈ A ⊓ B
    refine ⟨A.mul_mem (A.mul_mem g.2 x.2) (A.inv_mem g.2), ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (hBn (hAK g.2)) (x : W)).mp hx'.2
    simpa using this
  rcases shiftQs_normal_dichotomy hAq ((A ⊓ B).subgroupOf A) with hc | htop
  · intro x hx a ha
    have := Subgroup.mem_center_iff.mp
      (hc (show (⟨x, hx.1⟩ : ↥A) ∈ (A ⊓ B).subgroupOf A from hx)) ⟨a, ha⟩
    exact congrArg Subtype.val this
  · exfalso
    have hAB : A ≤ B := fun a ha => (show (⟨a, ha⟩ : ↥A) ∈ (A ⊓ B).subgroupOf A by
      rw [htop]; exact Subgroup.mem_top _).2
    have hM' : (A.subgroupOf B).Normal := by
      refine ⟨fun x hx g => ?_⟩
      have hx' : (x : W) ∈ A := hx
      show ((g * x * g⁻¹ : ↥B) : W) ∈ A
      have := (Subgroup.mem_normalizer_iff.mp (hAn (hBK g.2)) (x : W)).mp hx'
      simpa using this
    rcases shiftQs_normal_dichotomy hBq (A.subgroupOf B) with hc' | htop'
    · obtain ⟨a, b, hab⟩ := shiftQs_exists_noncomm hAq
      apply hab
      have := Subgroup.mem_center_iff.mp
        (hc' (show (⟨a, hAB a.2⟩ : ↥B) ∈ A.subgroupOf B from a.2)) ⟨b, hAB b.2⟩
      exact Subtype.ext (congrArg Subtype.val this).symm
    · apply hne
      refine le_antisymm hAB fun b hb => ?_
      exact (show (⟨b, hb⟩ : ↥B) ∈ A.subgroupOf B by rw [htop']; exact Subgroup.mem_top _)

theorem shiftComm_eq_bot {Kb N N' : Subgroup W}
    (hNK : N ≤ Kb) (hN'K : N' ≤ Kb) (hNn : Kb ≤ Subgroup.normalizer (N : Set W))
    (hN'n : Kb ≤ Subgroup.normalizer (N' : Set W)) (hNq : CFSG.IsQuasisimple ↥N)
    (hN'q : CFSG.IsQuasisimple ↥N') (hne : N ≠ N') : ⁅N, N'⁆ = ⊥ := by
  have h1 := shiftComm_inf_central hNK hN'K hNn hN'n hNq hN'q hne
  have hle : ⁅N, N'⁆ ≤ N ⊓ N' := by
    rw [Subgroup.commutator_le]
    intro n hn n' hn'
    refine ⟨?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (hNn (hN'K hn')) n⁻¹).mp (N.inv_mem hn)
      have e : ⁅n, n'⁆ = n * (n' * n⁻¹ * n'⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact N.mul_mem hn (by simpa using this)
    · have := (Subgroup.mem_normalizer_iff.mp (hN'n (hNK hn)) n').mp hn'
      have e : ⁅n, n'⁆ = (n * n' * n⁻¹) * n'⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact N'.mul_mem this (N'.inv_mem hn')
  have hcen : ∀ H : Subgroup W, H ≤ N ⊓ N' → ⁅H, N⁆ = ⊥ := by
    intro H hH
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (h1 g₁ (hH hg₁) g₂ hg₂).symm
  have h2 : ⁅⁅N, N'⁆, N⁆ = ⊥ := hcen _ hle
  have h3 : ⁅⁅N', N⁆, N⁆ = ⊥ := hcen _ (by rw [Subgroup.commutator_comm]; exact hle)
  have h4 : ⁅⁅N, N⁆, N'⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h3
  rw [shiftQs_commutator_self hNq] at h4
  exact h4

end Quasi

section Conj

variable {G : Type*} [Group G]

theorem shift_map_conj_mul (S : Subgroup G) (a b : G) :
    S.map (MulAut.conj (a * b)).toMonoidHom =
      (S.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem shift_map_conj_inv {S S' : Subgroup G} {g : G}
    (h : S.map (MulAut.conj g).toMonoidHom = S') :
    S'.map (MulAut.conj g⁻¹).toMonoidHom = S := by
  rw [← h, Subgroup.map_map]
  have : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [this, Subgroup.map_id]

theorem shift_mem_normalizer_iSup {ι : Type*} {S : ι → Subgroup G} {g : G}
    (hg : ∀ i, g ∈ Subgroup.normalizer (S i : Set G)) :
    g ∈ Subgroup.normalizer ((⨆ i, S i : Subgroup G) : Set G) := by
  have hmap : ∀ g' : G, (∀ i, g' ∈ Subgroup.normalizer (S i : Set G)) →
      (⨆ i, S i).map (MulAut.conj g').toMonoidHom ≤ ⨆ i, S i := by
    intro g' hg'
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => le_iSup_of_le i ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hg' i) x).mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hmap g hg ⟨x, hx, rfl⟩
  · intro hx
    have := hmap g⁻¹ (fun i => by simpa using (Subgroup.inv_mem _ (hg i))) ⟨_, hx, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

theorem shift_le_normalizer_of_comm {A B : Subgroup G}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : A ≤ Subgroup.normalizer (B : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ = y := by rw [h x hx y hy]; simp
    rw [this]
    exact hy
  · intro hz
    have hxz := h x hx _ hz
    have : x * y * x⁻¹ = y := by
      have h2 : x * (x * y * x⁻¹) = x * y := by
        rw [hxz]; simp [mul_assoc]
      exact mul_left_cancel h2
    rwa [this] at hz

theorem shift_le_normalizer_map {N S : Subgroup G} (ε : MulAut G)
    (hN : N ≤ Subgroup.normalizer (S : Set G)) (hsymm : ∀ g ∈ N, ε.symm g ∈ N) :
    N ≤ Subgroup.normalizer ((S.map ε.toMonoidHom : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hg' := hN (hsymm g hg)
  have key : ∀ y, y ∈ S.map ε.toMonoidHom ↔ ε.symm y ∈ S := fun y => Subgroup.mem_map_equiv
  rw [key, key]
  have := Subgroup.mem_normalizer_iff.mp hg' (ε.symm y)
  simpa using this

end Conj

section ShiftData

variable {G : Type*} [Group G]

structure ShiftData (C : Subgroup G) (Λ : Fin 3 → Subgroup G) (Tt : Subgroup G) : Prop where
  quasi : ∀ i, CFSG.IsQuasisimple (Λ i)
  comm : ∀ i j, i ≠ j → ∀ x ∈ Λ i, ∀ y ∈ Λ j, x * y = y * x
  Tcomm : ∀ x ∈ Tt, ∀ y ∈ Tt, x * y = y * x
  Tnorm : ∀ i, Tt ≤ Subgroup.normalizer (Λ i : Set G)
  le_C : ∀ i, Λ i ≤ C
  shift : ∀ g ∈ C, ∃ k : Fin 3, ∀ i, (Λ i).map (MulAut.conj g).toMonoidHom = Λ (i + k)
  zero : ∀ g ∈ C, (∀ i, (Λ i).map (MulAut.conj g).toMonoidHom = Λ i) → g ∈ Tt ⊔ ⨆ i, Λ i

variable {C Tt : Subgroup G} {Λ : Fin 3 → Subgroup G}

theorem ShiftData.ne (hD : ShiftData C Λ Tt) {i j : Fin 3} (hij : i ≠ j) : Λ i ≠ Λ j := by
  intro h
  obtain ⟨a, b, hab⟩ := shiftQs_exists_noncomm (hD.quasi i)
  apply hab
  have hb : (b : G) ∈ Λ j := by rw [← h]; exact b.2
  exact Subtype.ext (hD.comm i j hij a.1 a.2 b.1 hb)

theorem ShiftData.Tnorm_iSup (hD : ShiftData C Λ Tt) :
    Tt ≤ Subgroup.normalizer ((⨆ j, Λ j : Subgroup G) : Set G) :=
  fun _ ht => shift_mem_normalizer_iSup fun j => hD.Tnorm j ht

theorem ShiftData.iSup_le_normalizer (hD : ShiftData C Λ Tt) (j : Fin 3) :
    (⨆ i, Λ i : Subgroup G) ≤ Subgroup.normalizer (Λ j : Set G) := by
  refine iSup_le fun i => ?_
  by_cases hij : i = j
  · subst hij
    exact Subgroup.le_normalizer
  · exact shift_le_normalizer_of_comm (hD.comm i j hij)

theorem ShiftData.map_commutator (hD : ShiftData C Λ Tt) {g h : G} (hg : g ∈ C) (hh : h ∈ C)
    (i : Fin 3) : (Λ i).map (MulAut.conj ⁅g, h⁆).toMonoidHom = Λ i := by
  obtain ⟨a, ha⟩ := hD.shift g hg
  obtain ⟨b, hb⟩ := hD.shift h hh
  have ha' : ∀ j, (Λ j).map (MulAut.conj g⁻¹).toMonoidHom = Λ (j - a) := fun j =>
    shift_map_conj_inv (by rw [ha, sub_add_cancel])
  have hb' : ∀ j, (Λ j).map (MulAut.conj h⁻¹).toMonoidHom = Λ (j - b) := fun j =>
    shift_map_conj_inv (by rw [hb, sub_add_cancel])
  have e : ⁅g, h⁆ = g * (h * (g⁻¹ * h⁻¹)) := by rw [commutatorElement_def]; group
  rw [e, shift_map_conj_mul, shift_map_conj_mul, shift_map_conj_mul, hb' i, ha' (i - b),
    hb (i - b - a), ha (i - b - a + b)]
  congr 1
  abel

theorem shift_commutator_sup_le {Tt M : Subgroup G} (hc : ∀ x ∈ Tt, ∀ y ∈ Tt, x * y = y * x)
    (hn : Tt ≤ Subgroup.normalizer (M : Set G)) : ⁅Tt ⊔ M, Tt ⊔ M⁆ ≤ M := by
  have hnt : ∀ s ∈ Tt, ∀ z ∈ M, s * z * s⁻¹ ∈ M := fun s hs z hz =>
    (Subgroup.mem_normalizer_iff.mp (hn hs) z).mp hz
  have hdec : ∀ x ∈ Tt ⊔ M, ∃ t ∈ Tt, ∃ m ∈ M, t * m = x := by
    let S : Subgroup G :=
      { carrier := {x | ∃ t ∈ Tt, ∃ m ∈ M, t * m = x}
        mul_mem' := by
          rintro _ _ ⟨t, ht, m, hm, rfl⟩ ⟨t', ht', m', hm', rfl⟩
          refine ⟨t * t', Tt.mul_mem ht ht', t'⁻¹ * m * t' * m', M.mul_mem ?_ hm', by group⟩
          have := hnt t'⁻¹ (Tt.inv_mem ht') m hm
          simpa using this
        one_mem' := ⟨1, Tt.one_mem, 1, M.one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨t, ht, m, hm, rfl⟩
          exact ⟨t⁻¹, Tt.inv_mem ht, t * m⁻¹ * t⁻¹, hnt t ht _ (M.inv_mem hm), by group⟩ }
    have : Tt ⊔ M ≤ S :=
      sup_le (fun t ht => ⟨t, ht, 1, M.one_mem, by simp⟩)
        (fun m hm => ⟨1, Tt.one_mem, m, hm, by simp⟩)
    exact fun x hx => this hx
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨t, ht, m, hm, rfl⟩ := hdec x hx
  obtain ⟨t', ht', m', hm', rfl⟩ := hdec y hy
  have h1 : t'⁻¹ * m * t' ∈ M := by
    have := hnt t'⁻¹ (Tt.inv_mem ht') m hm
    simpa using this
  have htt : t' * t = t * t' := (hc t ht t' ht').symm
  have key : ⁅t * m, t' * m'⁆ =
      t' * ((t * ((t'⁻¹ * m * t') * m' * m⁻¹) * t⁻¹) * m'⁻¹) * t'⁻¹ := by
    have e : t' * ((t * ((t'⁻¹ * m * t') * m' * m⁻¹) * t⁻¹) * m'⁻¹) * t'⁻¹ =
        (t' * t) * t'⁻¹ * m * t' * m' * m⁻¹ * t⁻¹ * m'⁻¹ * t'⁻¹ := by group
    rw [e, htt, commutatorElement_def]
    group
  rw [key]
  have h2 : (t'⁻¹ * m * t') * m' * m⁻¹ ∈ M := M.mul_mem (M.mul_mem h1 hm') (M.inv_mem hm)
  have h3 : t * ((t'⁻¹ * m * t') * m' * m⁻¹) * t⁻¹ ∈ M := hnt t ht _ h2
  exact hnt t' ht' _ (M.mul_mem h3 (M.inv_mem hm'))

theorem ShiftData.le_iSup_of_perfect (hD : ShiftData C Λ Tt) {P : Subgroup G} (hPC : P ≤ C)
    (hP : ⁅P, P⁆ = P) : P ≤ ⨆ j, Λ j := by
  have hN0 : P ≤ Tt ⊔ ⨆ j, Λ j := by
    rw [← hP, Subgroup.commutator_le]
    intro x hx y hy
    refine hD.zero ⁅x, y⁆ ?_ (hD.map_commutator (hPC hx) (hPC hy))
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem (hPC hx) (hPC hy)) (C.inv_mem (hPC hx)))
      (C.inv_mem (hPC hy))
  calc P = ⁅P, P⁆ := hP.symm
    _ ≤ ⁅Tt ⊔ ⨆ j, Λ j, Tt ⊔ ⨆ j, Λ j⁆ := Subgroup.commutator_mono hN0 hN0
    _ ≤ ⨆ j, Λ j := shift_commutator_sup_le hD.Tcomm hD.Tnorm_iSup

theorem ShiftData.map_le_iSup (hD : ShiftData C Λ Tt) {ε : MulAut G} (hC : ∀ x ∈ C, ε x ∈ C)
    (i : Fin 3) : (Λ i).map ε.toMonoidHom ≤ ⨆ j, Λ j := by
  refine hD.le_iSup_of_perfect ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact hC x (hD.le_C i hx)
  · rw [← Subgroup.map_commutator, shiftQs_commutator_self (hD.quasi i)]

theorem ShiftData.map_iSup_eq (hD : ShiftData C Λ Tt) {ε : MulAut G} (hC : ∀ x ∈ C, ε x ∈ C)
    (hC' : ∀ x ∈ C, ε.symm x ∈ C) :
    (⨆ j, Λ j : Subgroup G).map ε.toMonoidHom = ⨆ j, Λ j := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_iSup]
    exact iSup_le fun i => hD.map_le_iSup hC i
  · intro x hx
    have h1 : ε.symm x ∈ ⨆ j, Λ j := by
      have : (⨆ j, Λ j : Subgroup G).map ε.symm.toMonoidHom ≤ ⨆ j, Λ j := by
        rw [Subgroup.map_iSup]
        exact iSup_le fun i => hD.map_le_iSup hC' i
      exact this ⟨x, hx, rfl⟩
    exact ⟨ε.symm x, h1, by simp⟩

theorem ShiftData.exists_map_eq (hD : ShiftData C Λ Tt) {ε : MulAut G}
    (hC : ∀ x ∈ C, ε x ∈ C) (hC' : ∀ x ∈ C, ε.symm x ∈ C) (i : Fin 3) :
    ∃ j, (Λ i).map ε.toMonoidHom = Λ j := by
  by_contra hcon
  push Not at hcon
  have hQM : (Λ i).map ε.toMonoidHom ≤ ⨆ j, Λ j := hD.map_le_iSup hC i
  have hQq : CFSG.IsQuasisimple ↥((Λ i).map ε.toMonoidHom) :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective (Λ i) ε.toMonoidHom ε.injective).symm (hD.quasi i)
  have hsymm : ∀ g ∈ (⨆ j, Λ j : Subgroup G), ε.symm g ∈ (⨆ j, Λ j : Subgroup G) := by
    intro g hg
    have : (⨆ j, Λ j : Subgroup G).map ε.symm.toMonoidHom ≤ ⨆ j, Λ j := by
      rw [Subgroup.map_iSup]
      exact iSup_le fun i => hD.map_le_iSup hC' i
    exact this ⟨g, hg, rfl⟩
  have hMQ : (⨆ j, Λ j : Subgroup G) ≤
      Subgroup.normalizer (((Λ i).map ε.toMonoidHom : Subgroup G) : Set G) :=
    shift_le_normalizer_map ε (hD.iSup_le_normalizer i) hsymm
  have hcomm : ∀ j, ⁅(Λ i).map ε.toMonoidHom, Λ j⁆ = ⊥ := fun j =>
    shiftComm_eq_bot hQM (le_iSup Λ j) hMQ (hD.iSup_le_normalizer j) hQq (hD.quasi j) (hcon j)
  obtain ⟨a, b, hab⟩ := shiftQs_exists_noncomm hQq
  apply hab
  have hcen : ∀ x ∈ (Λ i).map ε.toMonoidHom, (⨆ j, Λ j : Subgroup G) ≤
      Subgroup.centralizer {x} := by
    intro x hx
    refine iSup_le fun j y hy => ?_
    have h1 : ⁅x, y⁆ ∈ ⁅(Λ i).map ε.toMonoidHom, Λ j⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm j, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h1.symm
  have := hcen a.1 a.2 (hQM b.2)
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact Subtype.ext this.symm

theorem shift_fin3_translation (π : Fin 3 → Fin 3) (hinj : Function.Injective π)
    (h3 : ∀ i, π (π (π i)) = i) : ∃ k : Fin 3, ∀ i, π i = i + k := by
  revert π
  decide

theorem shift_map_pow_three (ε : MulAut G) (hε3 : ε ^ 3 = 1) (S : Subgroup G) :
    ((S.map ε.toMonoidHom).map ε.toMonoidHom).map ε.toMonoidHom = S := by
  have h3 : ∀ x, ε (ε (ε x)) = x := fun x => by
    have := congrArg (fun f : MulAut G => f x) hε3
    simpa [pow_succ, MulAut.mul_apply] using this
  ext x
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨_, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    simpa [h3] using hy
  · intro hx
    exact ⟨ε (ε x), ⟨ε x, ⟨x, hx, rfl⟩, rfl⟩, h3 x⟩

theorem ShiftData.exists_shift (hD : ShiftData C Λ Tt) {ε : MulAut G} (hε3 : ε ^ 3 = 1)
    (hC : ∀ x ∈ C, ε x ∈ C) (hC' : ∀ x ∈ C, ε.symm x ∈ C) :
    ∃ k : Fin 3, ∀ i, (Λ i).map ε.toMonoidHom = Λ (i + k) := by
  choose π hπ using hD.exists_map_eq hC hC'
  have hinj : Function.Injective π := by
    intro i i' h
    by_contra hne
    apply hD.ne hne
    have h2 : (Λ i).map ε.toMonoidHom = (Λ i').map ε.toMonoidHom := by rw [hπ, hπ, h]
    exact Subgroup.map_injective ε.injective h2
  have h3 : ∀ i, π (π (π i)) = i := by
    intro i
    by_contra hne
    apply hD.ne hne
    have : Λ (π (π (π i))) = Λ i := by
      rw [← hπ, ← hπ, ← hπ]
      exact shift_map_pow_three ε hε3 (Λ i)
    exact this
  obtain ⟨k, hk⟩ := shift_fin3_translation π hinj h3
  exact ⟨k, fun i => by rw [hπ, hk]⟩

end ShiftData

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
