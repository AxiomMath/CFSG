module

public import CFSG.GH74.KGroups.Generic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.GH74.KGroups

@[expose] noncomputable def conjCentralizerEquiv {G : Type*} [Group G] (S : Subgroup G) (g x0 : G)
    (hg : g ∈ S) :
    ↥(S ⊓ Subgroup.centralizer ({x0} : Set G)) ≃*
      ↥(S ⊓ Subgroup.centralizer ({g * x0 * g⁻¹} : Set G)) where
  toFun a := ⟨g * a.1 * g⁻¹, Subgroup.mem_inf.2 ⟨S.mul_mem (S.mul_mem hg
      (Subgroup.mem_inf.1 a.2).1) (S.inv_mem hg), by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 a.2).2
    calc g * a.1 * g⁻¹ * (g * x0 * g⁻¹) = g * (a.1 * x0) * g⁻¹ := by group
      _ = g * (x0 * a.1) * g⁻¹ := by rw [this]
      _ = g * x0 * g⁻¹ * (g * a.1 * g⁻¹) := by group⟩⟩
  invFun b := ⟨g⁻¹ * b.1 * g, Subgroup.mem_inf.2 ⟨S.mul_mem (S.mul_mem (S.inv_mem hg)
      (Subgroup.mem_inf.1 b.2).1) hg, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 b.2).2
    calc g⁻¹ * b.1 * g * x0 = g⁻¹ * (b.1 * (g * x0 * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x0 * g⁻¹) * b.1) * g := by rw [this]
      _ = x0 * (g⁻¹ * b.1 * g) := by group⟩⟩
  left_inv a := by ext; simp [mul_assoc]
  right_inv b := by ext; simp [mul_assoc]
  map_mul' a b := by ext; simp [mul_assoc]

theorem solvable_conj {G : Type*} [Group G] (S : Subgroup G) (g x0 : G) (hg : g ∈ S)
    (h : Group.IsSolvable ↥(S ⊓ Subgroup.centralizer ({x0} : Set G))) :
    Group.IsSolvable ↥(S ⊓ Subgroup.centralizer ({g * x0 * g⁻¹} : Set G)) :=
  Group.isSolvable_of_isSolvable_injective
    (f := (conjCentralizerEquiv S g x0 hg).symm.toMonoidHom)
    (conjCentralizerEquiv S g x0 hg).symm.injective

theorem card_conj {G : Type*} [Group G] (S : Subgroup G) (g x0 : G) (hg : g ∈ S) :
    Nat.card ↥(S ⊓ Subgroup.centralizer ({g * x0 * g⁻¹} : Set G)) =
      Nat.card ↥(S ⊓ Subgroup.centralizer ({x0} : Set G)) :=
  (Nat.card_congr (conjCentralizerEquiv S g x0 hg).toEquiv).symm

theorem commute_all_conj {G : Type*} [Group G] (A P : Subgroup G) (hPA : P ≤ A) (g x0 : G)
    (hg : g ∈ P)
    (h : ∀ σ ∈ A, (∀ q ∈ P ⊓ Subgroup.centralizer ({x0} : Set G), σ * q = q * σ) → σ ^ 2 = 1) :
    ∀ σ ∈ A, (∀ q ∈ P ⊓ Subgroup.centralizer ({g * x0 * g⁻¹} : Set G), σ * q = q * σ) →
      σ ^ 2 = 1 := by
  intro σ hσ hc
  have hgA : g ∈ A := hPA hg
  have key := h (g⁻¹ * σ * g) (A.mul_mem (A.mul_mem (A.inv_mem hgA) hσ) hgA) (by
    intro q hq
    obtain ⟨hqP, hqC⟩ := Subgroup.mem_inf.1 hq
    have h1 : g * q * g⁻¹ ∈ P ⊓ Subgroup.centralizer ({g * x0 * g⁻¹} : Set G) := by
      refine Subgroup.mem_inf.2 ⟨P.mul_mem (P.mul_mem hg hqP) (P.inv_mem hg), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_singleton_iff.1 hqC
      calc g * q * g⁻¹ * (g * x0 * g⁻¹) = g * (q * x0) * g⁻¹ := by group
        _ = g * (x0 * q) * g⁻¹ := by rw [this]
        _ = g * x0 * g⁻¹ * (g * q * g⁻¹) := by group
    have h2 := hc _ h1
    calc g⁻¹ * σ * g * q = g⁻¹ * (σ * (g * q * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * q * g⁻¹) * σ) * g := by rw [h2]
      _ = q * (g⁻¹ * σ * g) := by group)
  have h2 : (g⁻¹ * σ * g) ^ 2 = g⁻¹ * σ ^ 2 * g := by
    rw [pow_two, pow_two]; group
  rw [h2] at key
  calc σ ^ 2 = g * (g⁻¹ * σ ^ 2 * g) * g⁻¹ := by group
    _ = 1 := by rw [key]; group

theorem card_centralizer_inf_normal {H : Type*} [Group H] (N : Subgroup H) {G : Type*} [Group G]
    (P : Subgroup G) (e : N ≃* P) (x : N) :
    Nat.card ↥(Subgroup.centralizer ({(x : H)} : Set H) ⊓ N) =
      Nat.card ↥(P ⊓ Subgroup.centralizer ({(e x : G)} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun q => ⟨(e ⟨q.1, (Subgroup.mem_inf.1 q.2).2⟩ : G), Subgroup.mem_inf.2
        ⟨(e ⟨q.1, (Subgroup.mem_inf.1 q.2).2⟩).2, by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 q.2).1
          have h2 : (⟨q.1, (Subgroup.mem_inf.1 q.2).2⟩ : N) * x =
              x * ⟨q.1, (Subgroup.mem_inf.1 q.2).2⟩ := Subtype.ext h1
          have h3 := congrArg (fun z : N => (e z : G)) h2
          simpa using h3⟩⟩
      invFun := fun g => ⟨((e.symm ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩ : N) : H),
        Subgroup.mem_inf.2 ⟨by
          rw [Subgroup.mem_centralizer_singleton_iff]
          have h1 := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 g.2).2
          have h2 : e ((e.symm ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩) * x) =
              e (x * (e.symm ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩)) := by
            apply Subtype.ext
            simpa using h1
          have h3 := e.injective h2
          exact congrArg Subtype.val h3, (e.symm ⟨g.1, (Subgroup.mem_inf.1 g.2).1⟩).2⟩⟩
      left_inv := fun q => by
        apply Subtype.ext
        simp
      right_inv := fun g => by
        apply Subtype.ext
        simp }

section Action

variable {G : Type*} [Group G]

theorem AutModel.centralizer_trivial {K : Type*} [Group K] (M : AutModel K G) {σ : G}
    (hσ : σ ∈ M.A) (h : ∀ x ∈ M.P, σ * x = x * σ) : σ = 1 := by
  obtain ⟨φ, hφ⟩ := M.Φ.surjective ⟨σ, hσ⟩
  have hφσ : (M.Φ φ : G) = σ := congrArg Subtype.val hφ
  have h1 : φ = 1 := by
    ext x
    apply M.e.injective
    apply Subtype.ext
    rw [M.spec, hφσ]
    have := h (M.e x : G) (M.e x).2
    show σ * (M.e x : G) * σ⁻¹ = (M.e x : G)
    rw [this]
    group
  rw [← hφσ, h1, M.Φ_one]

@[expose] noncomputable def AutModel.actHom {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (M : AutModel N G) : H →* G :=
  (M.A.subtype.comp M.Φ.toMonoidHom).comp (MulAut.conjNormal (H := N))

theorem AutModel.actHom_mem {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (M : AutModel N G) (h : H) : M.actHom N h ∈ M.A :=
  (M.Φ (MulAut.conjNormal h)).2

theorem AutModel.actHom_spec {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (M : AutModel N G) (h : H) (x : N) :
    ((M.e (MulAut.conjNormal h x) : M.P) : G) =
      M.actHom N h * (M.e x : G) * (M.actHom N h)⁻¹ :=
  M.spec (MulAut.conjNormal h) x

theorem AutModel.actHom_injective {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hN : Subgroup.centralizer (N : Set H) = ⊥) (M : AutModel N G) :
    Function.Injective (M.actHom N) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro h hh
  have h1 : (M.Φ (MulAut.conjNormal h) : G) = 1 := hh
  have h2 : MulAut.conjNormal h = (1 : MulAut N) := (M.Φ_eq_one).1 h1
  rw [Subgroup.mem_bot]
  have : h ∈ Subgroup.centralizer (N : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h3 := congrArg (fun φ : MulAut N => ((φ ⟨n, hn⟩ : N) : H)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  rw [hN] at this
  simpa using this

theorem centralizer_solvable_of_model {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hN : Subgroup.centralizer (N : Set H) = ⊥) (M : AutModel N G) (x : N)
    (hS : Group.IsSolvable ↥(M.A ⊓ Subgroup.centralizer ({(M.e x : G)} : Set G))) :
    Group.IsSolvable ↥(Subgroup.centralizer ({(x : H)} : Set H)) := by
  let f : ↥(Subgroup.centralizer ({(x : H)} : Set H)) →*
      ↥(M.A ⊓ Subgroup.centralizer ({(M.e x : G)} : Set G)) :=
    { toFun := fun h => ⟨M.actHom N h.1, Subgroup.mem_inf.2 ⟨M.actHom_mem N h.1, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hc : (h.1 : H) * x * (h.1)⁻¹ = x := by
          have := Subgroup.mem_centralizer_singleton_iff.1 h.2
          rw [mul_inv_eq_iff_eq_mul]
          exact this
        have hx : MulAut.conjNormal (H := N) h.1 x = x := Subtype.ext (by simpa using hc)
        have h2 := M.actHom_spec N h.1 x
        rw [hx] at h2
        rw [eq_comm, mul_inv_eq_iff_eq_mul] at h2
        exact h2⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hf : Function.Injective f := by
    intro a b hab
    have h' := congrArg Subtype.val hab
    exact Subtype.ext (M.actHom_injective N hN h')
  exact Group.isSolvable_of_isSolvable_injective hf

theorem pPrimeCore_centralizer_eq_bot {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hN : Subgroup.centralizer (N : Set H) = ⊥) (M : AutModel N G) (x : N) (k : ℕ)
    (hQ : ∀ q ∈ Subgroup.centralizer ({(x : H)} : Set H) ⊓ N, q ^ (2 ^ k) = 1)
    (hA : ∀ σ ∈ M.A, (∀ g ∈ M.P ⊓ Subgroup.centralizer ({(M.e x : G)} : Set G),
      σ * g = g * σ) → σ ^ 2 = 1) :
    CFSG.pPrimeCore 2 ↥(Subgroup.centralizer ({(x : H)} : Set H)) = ⊥ := by
  set C := Subgroup.centralizer ({(x : H)} : Set H) with hC
  rw [CFSG.pPrimeCore, eq_bot_iff]
  refine sSup_le fun O hO => ?_
  obtain ⟨hOn, hOc⟩ := hO
  intro o ho
  rw [Subgroup.mem_bot]
  have hodd : ∀ c ∈ O, Nat.Coprime 2 (orderOf c) := fun c hc =>
    hOc.coprime_dvd_right (Subgroup.orderOf_dvd_natCard O hc)
  have hQn : (N.subgroupOf C).Normal := inferInstance
  have hcomm : ∀ q ∈ N.subgroupOf C, o * q = q * o := by
    intro q hq
    have hq1 : o * q * o⁻¹ * q⁻¹ ∈ O := by
      have h1 : q * o⁻¹ * q⁻¹ ∈ O := hOn.conj_mem _ (O.inv_mem ho) q
      have h2 := O.mul_mem ho h1
      simpa [mul_assoc] using h2
    have hq2 : o * q * o⁻¹ * q⁻¹ ∈ N.subgroupOf C := by
      have h1 : o * q * o⁻¹ ∈ N.subgroupOf C := hQn.conj_mem q hq o
      exact (N.subgroupOf C).mul_mem h1 ((N.subgroupOf C).inv_mem hq)
    set c := o * q * o⁻¹ * q⁻¹ with hc
    have hc2 : c ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      have h1 : ((c : C) : H) ∈ C ⊓ N := Subgroup.mem_inf.2 ⟨c.2, hq2⟩
      simpa using hQ _ h1
    have hord : orderOf c = 1 := by
      have h1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc2
      exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (hodd c hq1).symm) h1
    have h1 : c = 1 := orderOf_eq_one_iff.1 hord
    rw [hc] at h1
    calc o * q = (o * q * o⁻¹ * q⁻¹) * (q * o) := by group
      _ = q * o := by rw [h1, one_mul]
  have hsq : (M.actHom N (o : H)) ^ 2 = 1 := by
    apply hA _ (M.actHom_mem N (o : H))
    intro g hg
    obtain ⟨hgP, hgC⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨q0, hq0⟩ := M.e.surjective ⟨g, hgP⟩
    have hq0g : (M.e q0 : G) = g := congrArg Subtype.val hq0
    have hq0x : q0 * x = x * q0 := by
      apply M.e.injective
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.1 hgC
      simp only [map_mul, Subgroup.coe_mul]
      rw [hq0g]
      exact this
    have hq0C : ((q0 : N) : H) ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hq0x
    have hq : (⟨(q0 : H), hq0C⟩ : C) ∈ N.subgroupOf C := q0.2
    have h1 := hcomm _ hq
    have h2 : MulAut.conjNormal (H := N) (o : H) q0 = q0 := by
      apply Subtype.ext
      have := congrArg Subtype.val h1
      simp only [MulAut.conjNormal_apply]
      simp only [Subgroup.coe_mul] at this
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have h3 := M.actHom_spec N (o : H) q0
    rw [h2, hq0g] at h3
    calc M.actHom N (o : H) * g = (M.actHom N (o : H) * g * (M.actHom N (o : H))⁻¹) *
          M.actHom N (o : H) := by group
      _ = g * M.actHom N (o : H) := by rw [← h3]
  have ho2 : o ^ 2 = 1 := by
    apply Subtype.ext
    have : M.actHom N ((o : H) ^ 2) = M.actHom N 1 := by
      rw [map_pow, hsq, map_one]
    simpa using M.actHom_injective N hN this
  have hord : orderOf o = 1 := by
    have h1 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one ho2
    exact Nat.Coprime.eq_one_of_dvd (hodd o ho).symm h1
  exact orderOf_eq_one_iff.1 hord

end Action

end CFSG.GH74.KGroups
