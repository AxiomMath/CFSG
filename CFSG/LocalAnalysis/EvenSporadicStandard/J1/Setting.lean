module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

structure Setting (G : Type) [Group G] [Finite G] where
  z : G
  L : Subgroup G
  E : Subgroup G
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  order_z : orderOf z = 2
  centralizer_eq : centralizer ({z} : Set G) = L ⊔ zpowers z
  disjoint : Disjoint L (zpowers z)
  E_le : E ≤ L
  card_E : Nat.card E = 8
  sq_E : ∀ x ∈ E, x * x = 1
  sylow_E : ∀ P : Subgroup G, P ≤ L → IsPGroup 2 P →
    ∃ g ∈ L, P ≤ E.map (MulAut.conj g).toMonoidHom
  centralizer_E : centralizer (E : Set G) ⊓ L = E
  card_normalizer_E : Nat.card (normalizer (E : Set G) ⊓ L : Subgroup G) = 168

variable {G : Type} [Group G] [Finite G] (H : Setting G)

namespace Setting

@[expose] def V : Subgroup G := H.E ⊔ zpowers H.z

theorem z_mul_self : H.z * H.z = 1 := by
  rw [← pow_two, ← H.order_z, pow_orderOf_eq_one]

theorem z_inv : H.z⁻¹ = H.z := inv_eq_of_mul_eq_one_right H.z_mul_self

theorem z_ne_one : H.z ≠ 1 := by
  intro h
  have := H.order_z
  rw [h, orderOf_one] at this
  exact absurd this (by decide)

theorem comm_z {l : G} (hl : l ∈ H.L) : l * H.z = H.z * l := by
  have h : l ∈ centralizer ({H.z} : Set G) := H.centralizer_eq ▸ mem_sup_left hl
  exact mem_centralizer_singleton_iff.1 h

theorem z_not_mem_L : H.z ∉ H.L := by
  intro h
  have := H.disjoint.le_bot ⟨h, mem_zpowers _⟩
  exact H.z_ne_one (mem_bot.1 this)

theorem mem_centralizer_iff {x : G} :
    x ∈ centralizer ({H.z} : Set G) ↔ x ∈ H.L ∨ x * H.z ∈ H.L := by
  constructor
  · intro hx
    rw [H.centralizer_eq] at hx
    obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (A := H.L) (B := zpowers H.z) (zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun l hl =>
        (H.comm_z hl))) hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
    have hz2 : ∀ n : ℤ, H.z ^ n = 1 ∨ H.z ^ n = H.z := fun n => by
      rcases Int.emod_two_eq_zero_or_one n with h | h
      · left
        rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
        simp [← H.order_z]
      · right
        rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
        simp [← H.order_z]
    rcases hz2 n with h | h
    · left; rw [h, mul_one]; exact hl
    · right; rw [h, mul_assoc, H.z_mul_self, mul_one]; exact hl
  · rintro (h | h)
    · exact H.centralizer_eq ▸ mem_sup_left h
    · have : x = (x * H.z) * H.z⁻¹ := by group
      rw [this, H.centralizer_eq]
      exact mul_mem (mem_sup_left h) (inv_mem (mem_sup_right (mem_zpowers _)))


theorem E_comm {a b : G} (ha : a ∈ H.E) (hb : b ∈ H.E) : a * b = b * a := by
  have h1 := H.sq_E _ (mul_mem ha hb)
  have h2 := H.sq_E a ha
  have h3 := H.sq_E b hb
  have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3] at this
  exact this

theorem E_inv {a : G} (ha : a ∈ H.E) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (H.sq_E a ha)

theorem z_comm_E {e : G} (he : e ∈ H.E) : e * H.z = H.z * e := H.comm_z (H.E_le he)

theorem z_not_mem_E : H.z ∉ H.E := fun h => H.z_not_mem_L (H.E_le h)

open Classical in
noncomputable def projFun (x : centralizer ({H.z} : Set G)) : H.L :=
  if h : (x : G) ∈ H.L then ⟨x, h⟩
  else ⟨x * H.z, ((H.mem_centralizer_iff).1 x.2).resolve_left h⟩

theorem projFun_of_mem {x : centralizer ({H.z} : Set G)} (h : (x : G) ∈ H.L) :
    ((H.projFun x : H.L) : G) = x := by
  simp [projFun, h]

theorem projFun_of_not_mem {x : centralizer ({H.z} : Set G)} (h : (x : G) ∉ H.L) :
    ((H.projFun x : H.L) : G) = x * H.z := by
  simp [projFun, h]

noncomputable def proj : centralizer ({H.z} : Set G) →* H.L where
  toFun := H.projFun
  map_one' := by
    apply Subtype.ext
    rw [H.projFun_of_mem (x := 1) (one_mem _)]
    rfl
  map_mul' x y := by
    apply Subtype.ext
    have hxz : (x : G) * H.z = H.z * x := mem_centralizer_singleton_iff.1 x.2
    have hyz : (y : G) * H.z = H.z * y := mem_centralizer_singleton_iff.1 y.2
    have hmul : ((H.projFun x * H.projFun y : H.L) : G) =
        ((H.projFun x : H.L) : G) * (H.projFun y : H.L) := rfl
    by_cases hx : (x : G) ∈ H.L <;> by_cases hy : (y : G) ∈ H.L
    · have hxy : ((x * y : centralizer ({H.z} : Set G)) : G) ∈ H.L := mul_mem hx hy
      rw [hmul, H.projFun_of_mem hxy, H.projFun_of_mem hx, H.projFun_of_mem hy]
      rfl
    · have hxy : ((x * y : centralizer ({H.z} : Set G)) : G) ∉ H.L := fun h => hy (by
        have := mul_mem (inv_mem hx) h
        simpa using this)
      rw [hmul, H.projFun_of_not_mem hxy, H.projFun_of_mem hx, H.projFun_of_not_mem hy]
      change _ = (x : G) * ((y : G) * H.z)
      simp [mul_assoc]
    · have hxy : ((x * y : centralizer ({H.z} : Set G)) : G) ∉ H.L := fun h => hx (by
        have := mul_mem h (inv_mem hy)
        simpa using this)
      rw [hmul, H.projFun_of_not_mem hxy, H.projFun_of_not_mem hx, H.projFun_of_mem hy]
      change _ = (x : G) * H.z * (y : G)
      simp [mul_assoc, ← hyz]
    · have hxy : ((x * y : centralizer ({H.z} : Set G)) : G) ∈ H.L := by
        have h1 := (H.mem_centralizer_iff).1 x.2
        have h2 := (H.mem_centralizer_iff).1 y.2
        have hx' := h1.resolve_left hx
        have hy' := h2.resolve_left hy
        have := mul_mem hx' hy'
        have e : (x : G) * H.z * ((y : G) * H.z) = (x : G) * y := by
          calc (x : G) * H.z * ((y : G) * H.z) = (x : G) * (H.z * (y : G)) * H.z := by group
            _ = (x : G) * ((y : G) * H.z) * H.z := by rw [hyz]
            _ = (x : G) * y * (H.z * H.z) := by group
            _ = (x : G) * y := by rw [H.z_mul_self, mul_one]
        show (x : G) * (y : G) ∈ H.L
        rw [← e]
        exact this
      rw [hmul, H.projFun_of_mem hxy, H.projFun_of_not_mem hx, H.projFun_of_not_mem hy]
      change (x : G) * y = (x : G) * H.z * ((y : G) * H.z)
      calc (x : G) * y = (x : G) * y * (H.z * H.z) := by rw [H.z_mul_self, mul_one]
        _ = (x : G) * (y * H.z) * H.z := by group
        _ = (x : G) * (H.z * y) * H.z := by rw [hyz]
        _ = (x : G) * H.z * ((y : G) * H.z) := by group

theorem proj_val {x : centralizer ({H.z} : Set G)} :
    (x : G) = ((H.proj x : H.L) : G) ∨ (x : G) = ((H.proj x : H.L) : G) * H.z := by
  by_cases h : (x : G) ∈ H.L
  · left; exact (H.projFun_of_mem h).symm
  · right
    show (x : G) = ((H.projFun x : H.L) : G) * H.z
    rw [H.projFun_of_not_mem h]
    calc (x : G) = (x : G) * (H.z * H.z) := by rw [H.z_mul_self, mul_one]
      _ = (x : G) * H.z * H.z := by group

theorem exists_conj_le_V {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({H.z} : Set G)) :
    ∃ g ∈ H.L, P ≤ H.V.map (MulAut.conj g).toMonoidHom := by
  set C : Subgroup G := centralizer ({H.z} : Set G) with hC
  have hP' : IsPGroup 2 (P.comap C.subtype) := hP.comap_subtype
  set Q : Subgroup G := ((P.comap C.subtype).map H.proj).map H.L.subtype with hQ
  have hQp : IsPGroup 2 Q := (hP'.map H.proj).map _
  have hQL : Q ≤ H.L := by
    rintro _ ⟨l, _, rfl⟩
    exact l.2
  obtain ⟨g, hgL, hg⟩ := H.sylow_E Q hQL hQp
  have hzg : g * H.z * g⁻¹ = H.z := by
    have := H.comm_z hgL
    calc g * H.z * g⁻¹ = (H.z * g) * g⁻¹ := by rw [this]
      _ = H.z := by group
  refine ⟨g, hgL, fun x hx => ?_⟩
  set y : C := ⟨x, hPC hx⟩ with hy
  have hlQ : ((H.proj y : H.L) : G) ∈ Q := ⟨H.proj y, ⟨y, hx, rfl⟩, rfl⟩
  obtain ⟨e, he, hel⟩ := hg hlQ
  have hconj : ((MulAut.conj g).toMonoidHom e : G) = ((H.proj y : H.L) : G) := hel
  have hz' : (MulAut.conj g).toMonoidHom H.z = H.z := by
    simpa [MulAut.conj_apply] using hzg
  rcases H.proj_val (x := y) with h | h
  · refine ⟨e, mem_sup_left he, ?_⟩
    rw [hconj]
    exact h.symm
  · refine ⟨e * H.z, mul_mem (mem_sup_left he) (mem_sup_right (mem_zpowers _)), ?_⟩
    rw [map_mul, hz', hconj]
    exact h.symm


theorem mem_V_iff {x : G} : x ∈ H.V ↔ x ∈ H.E ∨ x * H.z ∈ H.E := by
  constructor
  · intro hx
    obtain ⟨e, he, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer (A := H.E)
      (B := zpowers H.z) (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun e he =>
        H.z_comm_E he)) hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hc
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      have : H.z ^ n = 1 := by
        rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
        simp [← H.order_z]
      rw [this, mul_one]; exact he
    · right
      have : H.z ^ n = H.z := by
        rw [← Int.emod_add_mul_ediv n 2, h, zpow_add, zpow_mul]
        simp [← H.order_z]
      rw [this, mul_assoc, H.z_mul_self, mul_one]; exact he
  · rintro (h | h)
    · exact mem_sup_left h
    · have : x = (x * H.z) * H.z⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left h) (inv_mem (mem_sup_right (mem_zpowers _)))

theorem E_le_V : H.E ≤ H.V := le_sup_left

theorem z_mem_V : H.z ∈ H.V := mem_sup_right (mem_zpowers _)

theorem mem_V_iff' {x : G} : x ∈ H.V ↔ x ∈ H.E ∨ ∃ e ∈ H.E, x = e * H.z := by
  rw [H.mem_V_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨x * H.z, h, ?_⟩
      calc x = x * (H.z * H.z) := by rw [H.z_mul_self, mul_one]
        _ = x * H.z * H.z := by group
  · rintro (h | ⟨e, he, rfl⟩)
    · exact Or.inl h
    · right
      have : e * H.z * H.z = e := by
        calc e * H.z * H.z = e * (H.z * H.z) := by group
          _ = e := by rw [H.z_mul_self, mul_one]
      rw [this]; exact he

theorem V_sq {x : G} (hx : x ∈ H.V) : x * x = 1 := by
  rcases H.mem_V_iff'.1 hx with h | ⟨e, he, rfl⟩
  · exact H.sq_E x h
  · have hc := H.z_comm_E he
    calc e * H.z * (e * H.z) = e * (H.z * e) * H.z := by group
      _ = e * (e * H.z) * H.z := by rw [← hc]
      _ = (e * e) * (H.z * H.z) := by group
      _ = 1 := by rw [H.sq_E e he, H.z_mul_self, mul_one]

theorem V_comm {a b : G} (ha : a ∈ H.V) (hb : b ∈ H.V) : a * b = b * a := by
  have h1 := H.V_sq (mul_mem ha hb)
  have h2 := H.V_sq ha
  have h3 := H.V_sq hb
  have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right h3] at this
  exact this

theorem V_le_centralizer : H.V ≤ centralizer ({H.z} : Set G) := by
  intro x hx
  rw [mem_centralizer_singleton_iff]
  exact H.V_comm hx H.z_mem_V |>.symm.symm


theorem card_V : Nat.card H.V = 16 := by
  have hE : zpowers H.z ≤ centralizer (H.E : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun e he => H.z_comm_E he)
  have hd : Disjoint H.E (zpowers H.z) := H.disjoint.mono_left H.E_le
  have := Nat.card_congr (mulEquivProdSup hE hd).toEquiv
  rw [Nat.card_prod, Nat.card_zpowers, H.order_z, H.card_E] at this
  unfold V
  omega

theorem centralizer_V : centralizer (H.V : Set G) = H.V := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hxz : x ∈ centralizer ({H.z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.1 hx H.z H.z_mem_V).symm
    have hxE : x ∈ centralizer (H.E : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun e he => Subgroup.mem_centralizer_iff.1 hx e (H.E_le_V he)
    rcases H.mem_centralizer_iff.1 hxz with h | h
    · exact H.E_le_V (H.centralizer_E ▸ (⟨hxE, h⟩ : x ∈ centralizer (H.E : Set G) ⊓ H.L))
    · have hxzE : x * H.z ∈ centralizer (H.E : Set G) := by
        refine mul_mem hxE (Subgroup.mem_centralizer_iff.2 fun e he => H.z_comm_E he)
      exact H.mem_V_iff.2 (Or.inr (H.centralizer_E ▸
        (⟨hxzE, h⟩ : x * H.z ∈ centralizer (H.E : Set G) ⊓ H.L)))
  · exact Subgroup.mem_centralizer_iff.2 fun v hv => H.V_comm hv hx

theorem star {P : Subgroup G} (hP : IsPGroup 2 P) (hPC : P ≤ centralizer ({H.z} : Set G)) :
    Nat.card P ≤ 16 ∧ ∀ x ∈ P, x * x = 1 := by
  obtain ⟨g, -, hg⟩ := H.exists_conj_le_V hP hPC
  refine ⟨?_, fun x hx => ?_⟩
  · calc Nat.card P ≤ Nat.card (H.V.map (MulAut.conj g).toMonoidHom) :=
        Subgroup.card_le_of_le hg
      _ = 16 := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, H.card_V]
  · obtain ⟨v, hv, hvx⟩ := hg hx
    rw [← hvx]
    have := H.V_sq hv
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    calc g * v * g⁻¹ * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [this]; group

theorem star_conj {w : G} (hw : IsConj H.z w) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizer ({w} : Set G)) : Nat.card P ≤ 16 ∧ ∀ x ∈ P, x * x = 1 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hw
  set P' : Subgroup G := P.map (MulAut.conj c⁻¹).toMonoidHom with hP'
  have hP'p : IsPGroup 2 P' := hP.map _
  have hP'C : P' ≤ centralizer ({H.z} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 (hPC hx)
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    have hz : H.z = c⁻¹ * w * c := by rw [← hc]; group
    rw [hz]
    calc c⁻¹ * x * c * (c⁻¹ * w * c) = c⁻¹ * (x * w) * c := by group
      _ = c⁻¹ * (w * x) * c := by rw [this]
      _ = c⁻¹ * w * c * (c⁻¹ * x * c) := by group
  obtain ⟨h1, h2⟩ := H.star hP'p hP'C
  refine ⟨?_, fun x hx => ?_⟩
  · rw [hP', Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective] at h1
    exact h1
  · have := h2 _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
      inv_inv] at this
    have h3 : c⁻¹ * (x * x) * c = 1 := by
      calc c⁻¹ * (x * x) * c = c⁻¹ * x * c * (c⁻¹ * x * c) := by group
        _ = 1 := this
    have := congrArg (fun y => c * y * c⁻¹) h3
    simpa [mul_assoc] using this

end Setting

end CFSG.EvenSporadicStandard.J1Std
