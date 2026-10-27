module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshFusion

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b
open scoped commutatorElement

section Tables

theorem rep_nwT {α k : ℕ} (D : FusionData α k) (W : List Int) :
    Rep 16 (nwT α k W) (wp α k (swN W)) :=
  rep_nT D.hsz D.hnC _

theorem tsub_wgens_le {α k : ℕ} (D : FusionData α k) {Ws : List (List Int)}
    (hperm : ∀ T ∈ wgens α k Ws, permOK 16 T = true) : tsub (wgens α k Ws) ≤ NG α k :=
  tsub_le_of_rep hperm fun T hT => by
    obtain ⟨W, -, rfl⟩ := mem_wgens.1 hT
    exact ⟨wp α k (swN W), wp_mem α k _, rep_nwT D W⟩

theorem tp_nwT {α k : ℕ} (D : FusionData α k) {W : List Int} (hp : permOK 16 (nwT α k W) = true) :
    tp 16 (nwT α k W) = wp α k (swN W) :=
  tp_eq_of_rep hp (rep_nwT D W)

end Tables

section Image

variable {G : Type} [Group G] {e : G}
variable {e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12}

set_option linter.unusedSectionVars false

variable {d : G} {α k : ℕ}

@[expose] noncomputable def img (E : NEmb e₀ d α k) (K : Subgroup (Equiv.Perm (Fin 16))) :
    Subgroup G :=
  (K.subgroupOf (NG α k)).map E.Ψ

theorem mem_img (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))} {y : G} :
    y ∈ img E K ↔ ∃ (g : Equiv.Perm (Fin 16)) (hg : g ∈ NG α k), g ∈ K ∧ E.Ψ ⟨g, hg⟩ = y := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.1, m.2, hm, rfl⟩
  · rintro ⟨g, hg, hK, rfl⟩
    exact ⟨⟨g, hg⟩, hK, rfl⟩

theorem Ψ_mem_img_iff (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))}
    {g : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) : E.Ψ ⟨g, hg⟩ ∈ img E K ↔ g ∈ K := by
  rw [mem_img]
  constructor
  · rintro ⟨g', hg', hK, h⟩
    have h2 : g' = g := congrArg Subtype.val (E.inj h)
    rwa [← h2]
  · intro hK
    exact ⟨g, hg, hK, rfl⟩

theorem img_le_Nn (E : NEmb e₀ d α k) (K : Subgroup (Equiv.Perm (Fin 16))) : img E K ≤ Nn e₀ := by
  intro y hy
  obtain ⟨g, hg, -, rfl⟩ := (mem_img E).1 hy
  rw [← E.range]
  exact ⟨⟨g, hg⟩, rfl⟩

theorem card_img (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))} (hK : K ≤ NG α k) :
    Nat.card (img E K) = Nat.card K := by
  unfold img
  rw [Subgroup.card_map_of_injective E.inj]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

theorem img_mono (E : NEmb e₀ d α k) {K₁ K₂ : Subgroup (Equiv.Perm (Fin 16))} (h : K₁ ≤ K₂) :
    img E K₁ ≤ img E K₂ := by
  intro y hy
  obtain ⟨g, hg, hK, rfl⟩ := (mem_img E).1 hy
  exact (mem_img E).2 ⟨g, hg, h hK, rfl⟩

@[expose] noncomputable def pull (E : NEmb e₀ d α k) (D : Subgroup G) :
    Subgroup (Equiv.Perm (Fin 16)) :=
  (D.comap E.Ψ).map (NG α k).subtype

theorem mem_pull (E : NEmb e₀ d α k) {D : Subgroup G} {x : Equiv.Perm (Fin 16)} :
    x ∈ pull E D ↔ ∃ hx : x ∈ NG α k, E.Ψ ⟨x, hx⟩ ∈ D := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hx, hD⟩
    exact ⟨⟨x, hx⟩, hD, rfl⟩

theorem pull_le (E : NEmb e₀ d α k) (D : Subgroup G) : pull E D ≤ NG α k := fun _ hx =>
  ((mem_pull E).1 hx).1

theorem img_pull (E : NEmb e₀ d α k) {D : Subgroup G} (hD : D ≤ Nn e₀) :
    img E (pull E D) = D := by
  ext y
  constructor
  · intro hy
    obtain ⟨g, hg, hK, rfl⟩ := (mem_img E).1 hy
    obtain ⟨_, hD'⟩ := (mem_pull E).1 hK
    exact hD'
  · intro hy
    have hy' : y ∈ E.Ψ.range := E.range ▸ hD hy
    obtain ⟨m, rfl⟩ := hy'
    exact (mem_img E).2 ⟨m.1, m.2, (mem_pull E).2 ⟨m.2, hy⟩, rfl⟩

theorem card_pull (E : NEmb e₀ d α k) {D : Subgroup G} (hD : D ≤ Nn e₀) :
    Nat.card (pull E D) = Nat.card D := by
  have h1 := card_img E (pull_le E D)
  rw [img_pull E hD] at h1
  exact h1.symm

theorem pull_le_of_le_img (E : NEmb e₀ d α k) {D : Subgroup G} {K : Subgroup (Equiv.Perm (Fin 16))}
    (h : D ≤ img E K) : pull E D ≤ K := by
  intro x hx
  obtain ⟨hx', hD⟩ := (mem_pull E).1 hx
  exact (Ψ_mem_img_iff E hx').1 (h hD)

theorem Ψ_mul (E : NEmb e₀ d α k) {g h : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k)
    (hh : h ∈ NG α k) :
    E.Ψ ⟨g, hg⟩ * E.Ψ ⟨h, hh⟩ = E.Ψ ⟨g * h, (NG α k).mul_mem hg hh⟩ :=
  (map_mul E.Ψ ⟨g, hg⟩ ⟨h, hh⟩).symm

theorem Ψ_inv (E : NEmb e₀ d α k) {g : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) :
    (E.Ψ ⟨g, hg⟩)⁻¹ = E.Ψ ⟨g⁻¹, (NG α k).inv_mem hg⟩ :=
  (map_inv E.Ψ ⟨g, hg⟩).symm

theorem Ψ_one (E : NEmb e₀ d α k) : E.Ψ ⟨1, (NG α k).one_mem⟩ = 1 := map_one E.Ψ

open scoped Classical in
@[expose] noncomputable def ψ (E : NEmb e₀ d α k) (g : Equiv.Perm (Fin 16)) : G :=
  if hg : g ∈ NG α k then E.Ψ ⟨g, hg⟩ else 1

theorem ψ_of_mem (E : NEmb e₀ d α k) {g : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) :
    ψ E g = E.Ψ ⟨g, hg⟩ := by
  unfold ψ
  rw [dif_pos hg]

theorem ψ_mul (E : NEmb e₀ d α k) {g h : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k)
    (hh : h ∈ NG α k) : ψ E (g * h) = ψ E g * ψ E h := by
  rw [ψ_of_mem E ((NG α k).mul_mem hg hh), ψ_of_mem E hg, ψ_of_mem E hh]
  exact (Ψ_mul E hg hh).symm

theorem ψ_one (E : NEmb e₀ d α k) : ψ E 1 = 1 := by
  rw [ψ_of_mem E (NG α k).one_mem]
  exact Ψ_one E

theorem ψ_inv (E : NEmb e₀ d α k) {g : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) :
    ψ E g⁻¹ = (ψ E g)⁻¹ := by
  rw [ψ_of_mem E ((NG α k).inv_mem hg), ψ_of_mem E hg]
  exact (Ψ_inv E hg).symm

theorem ψ_conj (E : NEmb e₀ d α k) {m g : Equiv.Perm (Fin 16)} (hm : m ∈ NG α k)
    (hg : g ∈ NG α k) : ψ E (m * g * m⁻¹) = ψ E m * ψ E g * (ψ E m)⁻¹ := by
  rw [ψ_mul E ((NG α k).mul_mem hm hg) ((NG α k).inv_mem hm), ψ_mul E hm hg, ψ_inv E hm]

theorem ψ_comm (E : NEmb e₀ d α k) {g h : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k)
    (hh : h ∈ NG α k) : ψ E ⁅g, h⁆ = ⁅ψ E g, ψ E h⁆ := by
  simp only [commutatorElement_def]
  rw [ψ_mul E ((NG α k).mul_mem ((NG α k).mul_mem hg hh) ((NG α k).inv_mem hg))
    ((NG α k).inv_mem hh), ψ_mul E ((NG α k).mul_mem hg hh) ((NG α k).inv_mem hg),
    ψ_mul E hg hh, ψ_inv E hg, ψ_inv E hh]

theorem ψ_mem_Nn (E : NEmb e₀ d α k) {g : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) :
    ψ E g ∈ Nn e₀ := by
  rw [ψ_of_mem E hg, ← E.range]
  exact ⟨⟨g, hg⟩, rfl⟩

theorem ψ_inj (E : NEmb e₀ d α k) {g h : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k)
    (hh : h ∈ NG α k) (hgh : ψ E g = ψ E h) : g = h := by
  rw [ψ_of_mem E hg, ψ_of_mem E hh] at hgh
  exact congrArg Subtype.val (E.inj hgh)

theorem exists_ψ (E : NEmb e₀ d α k) {y : G} (hy : y ∈ Nn e₀) :
    ∃ g : Equiv.Perm (Fin 16), g ∈ NG α k ∧ ψ E g = y := by
  have hy' : y ∈ E.Ψ.range := E.range ▸ hy
  obtain ⟨m, rfl⟩ := hy'
  exact ⟨m.1, m.2, ψ_of_mem E m.2⟩

theorem ψ_wp (E : NEmb e₀ d α k) (w : List (Fin 9 × Bool)) :
    ψ E (wp α k w) = val e₀ d α w := by
  rw [ψ_of_mem E (wp_mem α k w)]
  exact E.apply_wp w

theorem mem_img' (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))} {y : G} :
    y ∈ img E K ↔ ∃ g : Equiv.Perm (Fin 16), g ∈ NG α k ∧ g ∈ K ∧ ψ E g = y := by
  rw [mem_img]
  constructor
  · rintro ⟨g, hg, hK, rfl⟩
    exact ⟨g, hg, hK, ψ_of_mem E hg⟩
  · rintro ⟨g, hg, hK, rfl⟩
    exact ⟨g, hg, hK, (ψ_of_mem E hg).symm⟩

theorem ψ_mem_img (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))}
    {g : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) (hK : g ∈ K) : ψ E g ∈ img E K :=
  (mem_img' E).2 ⟨g, hg, hK, rfl⟩

theorem mem_of_ψ_mem_img (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))}
    {g : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) (h : ψ E g ∈ img E K) : g ∈ K := by
  obtain ⟨g', hg', hK, hgg⟩ := (mem_img' E).1 h
  rwa [← ψ_inj E hg' hg hgg]

theorem forall_mem_img' (E : NEmb e₀ d α k) {K : Subgroup (Equiv.Perm (Fin 16))} {φ : G → Prop} :
    (∀ y ∈ img E K, φ y) ↔ ∀ g : Equiv.Perm (Fin 16), g ∈ NG α k → g ∈ K → φ (ψ E g) := by
  constructor
  · intro h g hg hK
    exact h _ (ψ_mem_img E hg hK)
  · intro h y hy
    obtain ⟨g, hg, hK, rfl⟩ := (mem_img' E).1 hy
    exact h g hg hK

theorem Nn_inf_centralizer_eq (E : NEmb e₀ d α k) {g : Equiv.Perm (Fin 16)} (hg : g ∈ NG α k) :
    Nn e₀ ⊓ centralizer ({ψ E g} : Set G) =
      img E (centralizer ({g} : Set (Equiv.Perm (Fin 16))) ⊓ NG α k) := by
  ext y
  rw [Subgroup.mem_inf, mem_centralizer_singleton_iff, mem_img']
  constructor
  · rintro ⟨hy, hyc⟩
    obtain ⟨m, hm, rfl⟩ := exists_ψ E hy
    refine ⟨m, hm, Subgroup.mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, hm⟩, rfl⟩
    rw [← ψ_mul E hm hg, ← ψ_mul E hg hm] at hyc
    exact ψ_inj E ((NG α k).mul_mem hm hg) ((NG α k).mul_mem hg hm) hyc
  · rintro ⟨m, hm, hK, rfl⟩
    obtain ⟨hmc, -⟩ := Subgroup.mem_inf.1 hK
    refine ⟨ψ_mem_Nn E hm, ?_⟩
    rw [← ψ_mul E hm hg, ← ψ_mul E hg hm, mem_centralizer_singleton_iff.1 hmc]

theorem card_Nn_centralizer (D : FusionData α k) (E : NEmb e₀ d α k) {T : Table}
    {g : Equiv.Perm (Fin 16)} (hT : Rep 16 T g) (hg : g ∈ NG α k) :
    Nat.card (Nn e₀ ⊓ centralizer ({ψ E g} : Set G) : Subgroup G) =
      ((nEnum α k).toList.filter (commTT 16 T)).length := by
  rw [Nn_inf_centralizer_eq E hg, card_img E inf_le_right]
  have h := (nEnum_spec D.hnC).card_filter (fun x => g * x = x * g) (commTT 16 T)
    (fun T' hT' => commTT_iff hT ((nEnum_spec D.hnC).rep_mem hT').1)
  rw [closure_nGens_eq D.hsz] at h
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
  rw [Subgroup.mem_inf, mem_centralizer_singleton_iff, and_comm, eq_comm]

theorem exists_conj_Nn (E : NEmb e₀ d α k) {p₁ p₂ : Equiv.Perm (Fin 16)} (h1 : p₁ ∈ NG α k)
    (h2 : p₂ ∈ NG α k) (h : ∃ m ∈ NG α k, m * p₁ * m⁻¹ = p₂) :
    ∃ n ∈ Nn e₀, n * ψ E p₁ * n⁻¹ = ψ E p₂ := by
  obtain ⟨m, hm, rfl⟩ := h
  exact ⟨ψ E m, ψ_mem_Nn E hm, (ψ_conj E hm h1).symm⟩

end Image

end CFSG.EvenSporadicStandard.M12Std.Yosh
