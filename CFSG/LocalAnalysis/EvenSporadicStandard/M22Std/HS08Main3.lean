module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Main2
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Orbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.HS08Syl3

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup
open scoped Classical

theorem SqData.map {G G' : Type*} [Group G] [Group G'] (f : G →* G') (hf : Function.Injective f)
    {t z z' : G} {T : Subgroup G} (h : SqData t T z z') :
    SqData (f t) (T.map f) (f z) (f z') where
  t_mem := Subgroup.mem_map_of_mem f h.t_mem
  z_mem := Subgroup.mem_map_of_mem f h.z_mem
  z'_mem := Subgroup.mem_map_of_mem f h.z'_mem
  ne := fun e => h.ne (hf e)
  mul := by rw [← map_mul, h.mul]
  z_ne := fun e => h.z_ne (hf (by rw [e, map_one]))
  z'_ne := fun e => h.z'_ne (hf (by rw [e, map_one]))
  z_central := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, h.z_central x hx]
  z'_central := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, h.z'_central x hx]
  z_sq := by
    obtain ⟨x, hx, hxz⟩ := h.z_sq
    exact ⟨f x, Subgroup.mem_map_of_mem f hx, by rw [← map_mul, hxz]⟩
  z'_sq := by
    obtain ⟨x, hx, hxz⟩ := h.z'_sq
    exact ⟨f x, Subgroup.mem_map_of_mem f hx, by rw [← map_mul, hxz]⟩
  uniq := by
    rintro _ ⟨u, hu, rfl⟩ hc hu1 ⟨_, ⟨x, hx, rfl⟩, hxx⟩
    have hc' : ∀ y ∈ T, u * y = y * u := fun y hy =>
      hf (by rw [map_mul, map_mul]; exact hc (f y) (Subgroup.mem_map_of_mem f hy))
    have hu1' : u ≠ 1 := fun e => hu1 (by rw [e, map_one])
    have hsq : ∃ x ∈ T, x * x = u := ⟨x, hx, hf (by rw [map_mul]; exact hxx)⟩
    rcases h.uniq u hu hc' hu1' hsq with h1 | h1
    · exact Or.inl (by rw [h1])
    · exact Or.inr (by rw [h1])

theorem odd_card_conjOrb_of_sylow {G : Type*} [Group G] [Fintype G] (P : Sylow 2 G)
    (N : Subgroup G) (hPN : (P : Subgroup G) ≤ N) {w : G}
    (hw : ∀ x ∈ (P : Subgroup G), w * x = x * w) : Odd (conjOrb N w).card := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have heven : 2 ∣ (conjOrb N w).card := by
    rcases Nat.even_or_odd (conjOrb N w).card with h | h
    · exact even_iff_two_dvd.1 h
    · exact absurd h hodd
  have h1 := card_conjOrb_mul N w
  have hPst : (P : Subgroup G) ≤ N ⊓ centralizer ({w} : Set G) :=
    le_inf hPN fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hw x hx).symm
  have h2 : Nat.card (P : Subgroup G) ∣ Nat.card ↥(N ⊓ centralizer ({w} : Set G)) :=
    Subgroup.card_dvd_of_le hPst
  have h4 : 2 * Nat.card (P : Subgroup G) ∣ Nat.card N := by
    rw [← h1]
    exact mul_dvd_mul heven h2
  have h5 := h4.trans (Subgroup.card_subgroup_dvd_card N)
  rw [Sylow.card_eq_multiplicity P] at h5
  refine Nat.pow_succ_factorization_not_dvd (Nat.card_pos (α := G)).ne' Nat.prime_two ?_
  rwa [pow_succ, mul_comm]

namespace MainCtx

variable {G : Type} [Group G] {L : Subgroup G} {t : G} {Y : Type} [Group Y]
  {S J : Subgroup (MulAut Y)} (C : MainCtx G L t Y S J) [Finite G]
include C

theorem exists_sqData_G : ∃ z : ↥(centralizer ({t} : Set G)),
    SqData t (C.pre S) (z : G) ((z : G) * t) ∧ C.π z ∈ J ∧ C.π z ∈ innerImage Y ⊤ ∧
      C.π z ≠ 1 := by
  obtain ⟨z, hsq, hzJ, hzin, hz1, -⟩ := C.hπ.exists_sqData C.A
  exact ⟨z, hsq.map (centralizer ({t} : Set G)).subtype
    (centralizer ({t} : Set G)).subtype_injective, hzJ, hzin, hz1⟩

theorem card_pre_S : Nat.card (C.pre S) = 512 := by
  rw [C.card_pre, C.A.card_S]

omit [Finite G] in
theorem card_H : Nat.card ↥(centralizer ({t} : Set G)) = 2 * 887040 := by
  rw [C.hπ.card_Hh, C.A.card_A]

theorem isPGroup_pre_S : IsPGroup 2 (C.pre S) :=
  (C.hπ.isPGroup_comap_S C.A).map (centralizer ({t} : Set G)).subtype

theorem pre_S_maximal : ∀ P : Subgroup G, P ≤ centralizer ({t} : Set G) → IsPGroup 2 P →
    C.pre S ≤ P → P = C.pre S := by
  intro P hPH hP hTP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h1 : Nat.card P ∣ Nat.card ↥(centralizer ({t} : Set G)) := Subgroup.card_dvd_of_le hPH
  rw [C.card_H, hk] at h1
  have hk9 : k ≤ 9 := by
    by_contra hlt
    have h2 : 2 ^ 10 ∣ 2 * 887040 := (pow_dvd_pow 2 (by omega : 10 ≤ k)).trans h1
    norm_num at h2
  refine (Subgroup.eq_of_le_of_card_ge hTP ?_).symm
  rw [hk, C.card_pre_S]
  calc 2 ^ k ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) hk9
    _ = 512 := by norm_num

theorem exists_sylow : ∃ P : Sylow 2 G, (P : Subgroup G) = C.pre S := by
  obtain ⟨z, hsq, -⟩ := C.exists_sqData_G
  exact hsq.exists_sylow C.isPGroup_pre_S (C.pre_le_H S) C.pre_S_maximal

theorem not_conj_of_mem_L {u : G} (huL : u ∈ L) (hu2 : u * u = 1) (hu1 : u ≠ 1) (hut : u ≠ t)
    (g : G) : g * t * g⁻¹ ≠ u := by
  intro hg
  obtain ⟨z, hsq, hzJ, hzin, hz1⟩ := C.exists_sqData_G
  obtain ⟨P, hP⟩ := C.exists_sylow
  obtain ⟨c, -, hc⟩ := C.hinv z hzin hz1 (C.A.J_sq _ hzJ) u huL hu2 hu1 hut
  have hcg : (c * g) * t * (c * g)⁻¹ = c * u * c⁻¹ := by rw [← hg]; group
  rcases hc with hc | hc
  · have h1 := hsq.eq_of_conj P hP (g := c * g)
      (fun w hw => by rw [hcg, hc]; exact hsq.z_central w hw)
    rw [hcg, hc] at h1
    apply hsq.z'_ne
    rw [h1, C.t_sq]
  · have h1 := hsq.eq_of_conj P hP (g := c * g)
      (fun w hw => by rw [hcg, hc]; exact hsq.z'_central w hw)
    rw [hcg, hc] at h1
    apply hsq.z_ne
    exact mul_right_cancel (b := t) (by rw [h1, one_mul])

theorem not_mem_L_of_conj {g : G} (hne : g * t * g⁻¹ ≠ t) : g * t * g⁻¹ ∉ L := by
  intro hL
  refine C.not_conj_of_mem_L hL ?_ ?_ hne g rfl
  · calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [C.t_sq]; group
  · intro h1
    apply C.t_ne
    calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group

theorem weakly_closed (P : Sylow 2 G) (hP : (P : Subgroup G) = C.pre S) :
    ∀ g : G, (∀ x ∈ C.pre J, g * x * g⁻¹ ∈ (P : Subgroup G)) →
      ∀ x, x ∈ C.pre J ↔ g * x * g⁻¹ ∈ C.pre J := by
  intro g hg
  set E' : Subgroup G := (C.pre J).map (MulAut.conj g).toMonoidHom with hE'
  have hE'mem : ∀ y, y ∈ E' ↔ ∃ x ∈ C.pre J, g * x * g⁻¹ = y := by
    intro y
    simp [hE', Subgroup.mem_map, MulAut.conj_apply]
  have hE'T : E' ≤ C.pre S := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (hE'mem y).1 hy
    rw [← hP]
    exact hg x hx
  have hE'H : E' ≤ centralizer ({t} : Set G) := hE'T.trans (C.pre_le_H S)
  set F : Subgroup ↥(centralizer ({t} : Set G)) := E'.subgroupOf (centralizer ({t} : Set G))
    with hF
  have hFmem : ∀ y : ↥(centralizer ({t} : Set G)), y ∈ F ↔ (y : G) ∈ E' := fun y =>
    Subgroup.mem_subgroupOf
  have hFS : F ≤ S.comap C.π := fun y hy => (C.mem_pre_coe y).1 (hE'T ((hFmem y).1 hy))
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, hax⟩ := (hE'mem _).1 ((hFmem x).1 hx)
    obtain ⟨b, hb, hby⟩ := (hE'mem _).1 ((hFmem y).1 hy)
    apply Subtype.ext
    show (x : G) * y = y * x
    rw [← hax, ← hby]
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [C.E_comm ha hb]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group
  have hFsq : ∀ x ∈ F, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, hax⟩ := (hE'mem _).1 ((hFmem x).1 hx)
    apply Subtype.ext
    show (x : G) * x = 1
    rw [← hax]
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [C.E_sq ha]; group
  have hcard : Nat.card F = 64 := by
    have h1 : Nat.card F = Nat.card E' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE'H).toEquiv
    have h2 : Nat.card (C.pre J) = Nat.card E' := Nat.card_congr
      (Subgroup.equivMapOfInjective (C.pre J) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toEquiv
    rw [h1, ← h2]
    exact C.card_E
  have hFJ : F = J.comap C.π := C.hπ.elementary_le C.A hFS hFc hFsq hcard
  intro x
  constructor
  · intro hx
    have hy : g * x * g⁻¹ ∈ E' := (hE'mem _).2 ⟨x, hx, rfl⟩
    have hyH : g * x * g⁻¹ ∈ centralizer ({t} : Set G) := hE'H hy
    have : (⟨g * x * g⁻¹, hyH⟩ : ↥(centralizer ({t} : Set G))) ∈ J.comap C.π := by
      rw [← hFJ, hFmem]
      exact hy
    exact (C.mem_pre_coe ⟨_, hyH⟩).2 this
  · intro hx
    have hyH : g * x * g⁻¹ ∈ centralizer ({t} : Set G) := C.pre_le_H J hx
    have h1 : (⟨g * x * g⁻¹, hyH⟩ : ↥(centralizer ({t} : Set G))) ∈ F := by
      rw [hFJ]
      exact (C.mem_pre_coe ⟨_, hyH⟩).1 hx
    obtain ⟨x', hx', hx'x⟩ := (hE'mem _).1 ((hFmem _).1 h1)
    have : x' = x := mul_left_cancel (mul_right_cancel hx'x)
    rw [← this]
    exact hx'

theorem exists_fusion {g : G} (hg : g * t * g⁻¹ ∈ C.pre J) :
    ∃ n : G, (∀ w, w ∈ C.pre J ↔ n * w * n⁻¹ ∈ C.pre J) ∧ n * t * n⁻¹ = g * t * g⁻¹ := by
  obtain ⟨P, hP⟩ := C.exists_sylow
  exact exists_normalizing_conj_of_weakly_closed P (E := C.pre J)
    (by rw [hP]; exact C.E_le_pre_S) (fun x hx y hy => C.E_comm hx hy)
    (C.weakly_closed P hP) C.t_mem_pre hg rfl

theorem exists_odd_orbits [Fintype G] : ∃ z : ↥(centralizer ({t} : Set G)),
    C.π z ∈ J ∧ C.π z ∈ innerImage Y ⊤ ∧ C.π z ≠ 1 ∧
      Odd (conjOrb (normalizer ((C.pre J : Subgroup G) : Set G)) (z : G)).card ∧
      Odd (conjOrb (normalizer ((C.pre J : Subgroup G) : Set G)) (t * (z : G))).card := by
  obtain ⟨z, hsq, hzJ, hzin, hz1⟩ := C.exists_sqData_G
  obtain ⟨P, hP⟩ := C.exists_sylow
  have hPN : (P : Subgroup G) ≤ normalizer ((C.pre J : Subgroup G) : Set G) :=
    hP ▸ C.pre_S_le_normalizer
  refine ⟨z, hzJ, hzin, hz1, odd_card_conjOrb_of_sylow P _ hPN fun x hx => ?_,
    odd_card_conjOrb_of_sylow P _ hPN fun x hx => ?_⟩
  · rw [hP] at hx
    exact hsq.z_central x hx
  · rw [hP] at hx
    rw [show t * (z : G) = (z : G) * t from
      (Subgroup.mem_centralizer_singleton_iff.1 z.2).symm]
    exact hsq.z'_central x hx

end MainCtx

end CFSG.EvenSporadicStandard.M22Std
