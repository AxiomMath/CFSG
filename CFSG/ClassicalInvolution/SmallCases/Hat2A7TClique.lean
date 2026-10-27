module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Tight

public section

namespace CFSG.ClassicalInvolution.Hat2A7T

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Hat2A7

section Members

variable {F : Type*} [Group F]

@[expose] def IsMember (L : Subgroup F) : Prop := ∃ u : F, IsClassical2A7 ⊤ L u

@[expose] def CenterTrivial (F : Type*) [Group F] : Prop :=
  ∀ x : F, (∀ y : F, x * y = y * x) → x = 1

theorem centralizer_ne_top_of_orderOf_eq_two (hZ : CenterTrivial F) {x : F} (hx : orderOf x = 2) :
    Subgroup.centralizer ({x} : Set F) ≠ ⊤ := by
  intro h
  have hx1 : x = 1 := hZ x fun y => by
    have hy : y ∈ Subgroup.centralizer ({x} : Set F) := h ▸ Subgroup.mem_top y
    exact Subgroup.mem_centralizer_iff.mp hy x rfl
  rw [hx1, orderOf_one] at hx
  omega

theorem commOrEq_of_le_centralizer (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F)
    {x : F} (hx : orderOf x = 2) {L M : Subgroup F} (hL : IsMember L) (hM : IsMember M)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set F))
    (hMx : M ≤ Subgroup.centralizer ({x} : Set F)) : CommOrEq L M := by
  obtain ⟨u, hu⟩ := hL
  obtain ⟨v, hv⟩ := hM
  exact IH x hx (centralizer_ne_top_of_orderOf_eq_two hZ hx) L M u v (hu.mono hLx le_top)
    (hv.mono hMx le_top)

theorem le_centralizer_of_commOrEq {L N : Subgroup F} {u : F} (hN : IsClassical2A7 ⊤ N u)
    (h : CommOrEq L N) : L ≤ Subgroup.centralizer ({u} : Set F) := by
  intro l hl
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases h with rfl | h
  · exact hN.mul_comm_of_mem hl
  · exact h l hl u hN.mem

theorem commOrEq_trans (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F) {K N M : Subgroup F}
    (hK : IsMember K) (hN : IsMember N) (hM : IsMember M) (h1 : CommOrEq K N)
    (h2 : CommOrEq N M) : CommOrEq K M := by
  obtain ⟨u, hu⟩ := hN
  exact commOrEq_of_le_centralizer hZ IH hu.orderOf_eq_two hK hM
    (le_centralizer_of_commOrEq hu h1) (le_centralizer_of_commOrEq hu h2.symm)

end Members

section Clique

variable {F : Type*} [Group F]

@[expose] def cliqueInv (K : Subgroup F) : Set F :=
  {u | ∃ N : Subgroup F, IsClassical2A7 ⊤ N u ∧ CommOrEq K N}

@[expose] def cliqueGrp (K : Subgroup F) : Subgroup F := Subgroup.closure (cliqueInv K)

theorem mem_cliqueInv_self {K : Subgroup F} {z : F} (hK : IsClassical2A7 ⊤ K z) :
    z ∈ cliqueInv K :=
  ⟨K, hK, CommOrEq.refl K⟩

variable (hZ : CenterTrivial F) (IH : ClassicalCommuteBelow F)

include hZ IH in
theorem le_centralizer_cliqueInv {K N : Subgroup F} (hK : IsMember K) (hN : IsMember N)
    (hKN : CommOrEq K N) {u : F} (hu : u ∈ cliqueInv K) :
    N ≤ Subgroup.centralizer ({u} : Set F) := by
  obtain ⟨N₁, hN₁, hKN₁⟩ := hu
  exact le_centralizer_of_commOrEq hN₁
    (commOrEq_trans hZ IH hN hK ⟨u, hN₁⟩ hKN.symm hKN₁)

include hZ IH in
theorem cliqueInv_comm {K : Subgroup F} (hK : IsMember K) {u v : F} (hu : u ∈ cliqueInv K)
    (hv : v ∈ cliqueInv K) : u * v = v * u := by
  obtain ⟨N, hN, hKN⟩ := hu
  have h := le_centralizer_cliqueInv hZ IH hK ⟨u, hN⟩ hKN hv
  exact Subgroup.mem_centralizer_singleton_iff.mp (h hN.mem)

include hZ IH in
theorem le_centralizer_cliqueGrp {K N : Subgroup F} (hK : IsMember K) (hN : IsMember N)
    (hKN : CommOrEq K N) {a : F} (ha : a ∈ cliqueGrp K) :
    N ≤ Subgroup.centralizer ({a} : Set F) := by
  have key : cliqueGrp K ≤ Subgroup.centralizer (N : Set F) := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    intro n hn
    have := le_centralizer_cliqueInv hZ IH hK hN hKN hu hn
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp (key ha) n hn)

include hZ IH in
theorem cliqueGrp_comm {K : Subgroup F} (hK : IsMember K) {a b : F} (ha : a ∈ cliqueGrp K)
    (hb : b ∈ cliqueGrp K) : a * b = b * a := by
  have h1 : cliqueGrp K ≤ Subgroup.centralizer ({a} : Set F) := by
    refine (Subgroup.closure_le _).mpr fun u hu => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h2 : cliqueGrp K ≤ Subgroup.centralizer ({u} : Set F) := by
      refine (Subgroup.closure_le _).mpr fun v hv => ?_
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h' hh'
      rw [Set.mem_singleton_iff] at hh'
      rw [hh']
      exact cliqueInv_comm hZ IH hK hu hv
    exact (Subgroup.mem_centralizer_iff.mp (h2 ha) u rfl).symm
  exact Subgroup.mem_centralizer_iff.mp (h1 hb) a rfl

include hZ IH in
theorem cliqueGrp_sq {K : Subgroup F} (hK : IsMember K) {a : F} (ha : a ∈ cliqueGrp K) :
    a * a = 1 := by
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨N, hN, -⟩ := hx
    exact hN.mul_self
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hc := cliqueGrp_comm hZ IH hK hx hy
    calc x * y * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y) * y := by rw [← hc]
      _ = (x * x) * (y * y) := by group
      _ = 1 := by rw [ihx, ihy]; group
  | inv x hx ih =>
    calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
      _ = 1 := by rw [ih]; simp

include hZ IH in
theorem orderOf_eq_two_of_mem_cliqueGrp {K : Subgroup F} (hK : IsMember K) {a : F}
    (ha : a ∈ cliqueGrp K) (ha1 : a ≠ 1) : orderOf a = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact cliqueGrp_sq hZ IH hK ha) ha1

include hZ IH in
theorem mem_clique_iff_le_centralizer {K N : Subgroup F} (hK : IsMember K) (hN : IsMember N)
    {a : F} (ha : a ∈ cliqueGrp K) (ha1 : a ≠ 1) :
    N ≤ Subgroup.centralizer ({a} : Set F) ↔ CommOrEq K N := by
  constructor
  · intro h
    exact commOrEq_of_le_centralizer hZ IH (orderOf_eq_two_of_mem_cliqueGrp hZ IH hK ha ha1) hK hN
      (le_centralizer_cliqueGrp hZ IH hK hK (CommOrEq.refl K) ha) h
  · intro h
    exact le_centralizer_cliqueGrp hZ IH hK hN h ha


theorem isMember_map_conj {L : Subgroup F} (hL : IsMember L) (g : F) :
    IsMember (L.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨u, hu⟩ := hL
  refine ⟨g * u * g⁻¹, ?_⟩
  have h1 := hu.conj g
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at h1

theorem map_conj_le_centralizer {L : Subgroup F} {a : F}
    (h : L ≤ Subgroup.centralizer ({a} : Set F)) (g : F) :
    L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({g * a * g⁻¹} : Set F) := by
  rintro _ ⟨l, hl, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : l * a = a * l := Subgroup.mem_centralizer_singleton_iff.mp (h hl)
  show g * l * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * l * g⁻¹)
  calc g * l * g⁻¹ * (g * a * g⁻¹) = g * (l * a) * g⁻¹ := by group
    _ = g * (a * l) * g⁻¹ := by rw [h1]
    _ = g * a * g⁻¹ * (g * l * g⁻¹) := by group

include hZ IH in
theorem commOrEq_conj_of_mem_cliqueGrp {K : Subgroup F} (hK : IsMember K) {a : F}
    (ha : a ∈ cliqueGrp K) (ha1 : a ≠ 1) {g : F} (hga : g * a * g⁻¹ ∈ cliqueGrp K) :
    CommOrEq K (K.map (MulAut.conj g).toMonoidHom) := by
  have hga1 : g * a * g⁻¹ ≠ 1 := by
    intro h
    apply ha1
    have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [this, h]
    group
  have hKa : K ≤ Subgroup.centralizer ({a} : Set F) :=
    le_centralizer_cliqueGrp hZ IH hK hK (CommOrEq.refl K) ha
  exact (mem_clique_iff_le_centralizer hZ IH hK (isMember_map_conj hK g) hga hga1).mp
    (map_conj_le_centralizer hKa g)

include hZ IH in
theorem commOrEq_conj_of_mem_centralizer {K : Subgroup F} (hK : IsMember K) {a : F}
    (ha : a ∈ cliqueGrp K) (ha1 : a ≠ 1) {g : F} (hg : g * a = a * g) :
    CommOrEq K (K.map (MulAut.conj g).toMonoidHom) := by
  refine commOrEq_conj_of_mem_cliqueGrp hZ IH hK ha ha1 ?_
  have : g * a * g⁻¹ = a := by rw [hg]; group
  rwa [this]

end Clique

end CFSG.ClassicalInvolution.Hat2A7T
