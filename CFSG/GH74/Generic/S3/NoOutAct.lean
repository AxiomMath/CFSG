module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.Generic.S3.LinEvenInv
public import CFSG.GH74.Generic.S3.NbrR
public import CFSG.GH74.Generic.S3.V1InnerUni

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup
open CFSG.GH74.KGroups.L3Eps (InvDataB4)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.GH74.KGroups.Bal (lift_fixed)
open CFSG.QuasithinUnique.Setup.X5 (normalizerAct normalizerAct_of_mem normalizerAct_apply_mk coe_conjOn conjOn
  mem_centralizer_of_normalizerAct_eq_one eq_one_of_involution_mem_odd)
open scoped commutatorElement

section Act

variable {G : Type} [Group G]

theorem exists_inner_of_actMemInner {M : Subgroup G} [Group.IsPerfect M] {z : G}
    (hzN : z ∈ normalizer (M : Set G))
    (h : normalizerAct M ⟨z, hzN⟩ ∈ (inner (↥M ⧸ center ↥M) : Subgroup (MulAut (↥M ⧸ center ↥M)))) :
    ∃ m ∈ M, ∀ n ∈ M, z * n * z⁻¹ = m * n * m⁻¹ := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
  have h1 : normalizerAct M ⟨z, hzN⟩ = normalizerAct M ⟨(m : G), Subgroup.le_normalizer m.2⟩ := by
    rw [normalizerAct_of_mem M m.2]
    exact hy.symm
  have h2 : normalizerAct M (⟨z, hzN⟩ * ⟨(m : G), Subgroup.le_normalizer m.2⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, h1, mul_inv_cancel]
  have hc := mem_centralizer_of_normalizerAct_eq_one M h2
  have hc' : z * (m : G)⁻¹ ∈ centralizer (M : Set G) := by simpa using hc
  refine ⟨m, m.2, fun n hn => ?_⟩
  have hn' : (m : G) * n * (m : G)⁻¹ ∈ M := M.mul_mem (M.mul_mem m.2 hn) (M.inv_mem m.2)
  have h3 := Subgroup.mem_centralizer_iff.1 hc' _ hn'
  calc z * n * z⁻¹ = (z * (m : G)⁻¹) * ((m : G) * n * (m : G)⁻¹) * (z * (m : G)⁻¹)⁻¹ := by group
    _ = ((m : G) * n * (m : G)⁻¹ * (z * (m : G)⁻¹)) * (z * (m : G)⁻¹)⁻¹ := by rw [← h3]
    _ = (m : G) * n * (m : G)⁻¹ := by group

theorem normalizerAct_mul_centralizer {M : Subgroup G} {a c : G} (haM : a ∈ M)
    (hcc : c ∈ centralizer (M : Set G)) (hN : a * c ∈ normalizer (M : Set G)) :
    normalizerAct M ⟨a * c, hN⟩ = MulAut.conj (QuotientGroup.mk ⟨a, haM⟩ : ↥M ⧸ center ↥M) := by
  ext s
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective s
  rw [normalizerAct_apply_mk, MulAut.conj_apply]
  have hcn : (c : G) * n = n * c := (Subgroup.mem_centralizer_iff.1 hcc _ n.2).symm
  change (QuotientGroup.mk (conjOn M ⟨a * c, hN⟩ n) : ↥M ⧸ center ↥M) =
    QuotientGroup.mk (⟨a, haM⟩ * n * ⟨a, haM⟩⁻¹)
  congr 1
  apply Subtype.ext
  rw [coe_conjOn]
  show a * c * (n : G) * (a * c)⁻¹ = a * (n : G) * a⁻¹
  calc a * c * (n : G) * (a * c)⁻¹ = a * (c * n) * c⁻¹ * a⁻¹ := by group
    _ = a * (n * c) * c⁻¹ * a⁻¹ := by rw [hcn]
    _ = a * (n : G) * a⁻¹ := by group

theorem zStar_conj [Finite G] (g : G) {u x : G} {O : Subgroup G} (hOodd : Odd (Nat.card O))
    (hOnorm : ∀ c ∈ centralizer ({u} : Set G), ∀ o ∈ O, c * o * c⁻¹ ∈ O)
    (hZ : ∀ h ∈ centralizer ({u} : Set G), h * x * h⁻¹ * x⁻¹ ∈ O) :
    ∃ O'' : Subgroup G, Odd (Nat.card O'') ∧
      (∀ c ∈ centralizer ({g⁻¹ * u * g} : Set G), ∀ o ∈ O'', c * o * c⁻¹ ∈ O'') ∧
      ∀ h ∈ centralizer ({g⁻¹ * u * g} : Set G), h * (g⁻¹ * x * g) * h⁻¹ * (g⁻¹ * x * g)⁻¹ ∈ O'' := by
  refine ⟨O.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hOodd
  · rintro c hc _ ⟨o, ho, rfl⟩
    have hc' : g * c * g⁻¹ ∈ centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      have : c * (g⁻¹ * u * g) = (g⁻¹ * u * g) * c := hc
      calc g * c * g⁻¹ * u = g * (c * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * c) * g⁻¹ := by rw [this]
        _ = u * (g * c * g⁻¹) := by group
    refine ⟨(g * c * g⁻¹) * o * (g * c * g⁻¹)⁻¹, hOnorm _ hc' o ho, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · intro h hh
    have hh' : g * h * g⁻¹ ∈ centralizer ({u} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hh ⊢
      have : h * (g⁻¹ * u * g) = (g⁻¹ * u * g) * h := hh
      calc g * h * g⁻¹ * u = g * (h * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * h) * g⁻¹ := by rw [this]
        _ = u * (g * h * g⁻¹) := by group
    refine ⟨(g * h * g⁻¹) * x * (g * h * g⁻¹)⁻¹ * x⁻¹, hZ _ hh', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem exists_R_of_zStar [Finite G] {M : Subgroup G} (hodd : Odd (Nat.card (center ↥M))) {a e : G}
    (haN : a ∈ normalizer (M : Set G)) (he2 : e * e = 1) (heN : e ∈ normalizer (M : Set G))
    {O : Subgroup G} (hOodd : Odd (Nat.card O))
    (hOnorm : ∀ c ∈ centralizer ({e} : Set G), ∀ o ∈ O, c * o * c⁻¹ ∈ O)
    (hZ : ∀ h ∈ centralizer ({e} : Set G), h * a * h⁻¹ * a⁻¹ ∈ O) :
    ∃ R : Subgroup (↥M ⧸ center ↥M), Odd (Nat.card R) ∧
      (∀ s : ↥M ⧸ center ↥M, normalizerAct M ⟨e, heN⟩ s = s → ∀ r ∈ R, s * r * s⁻¹ ∈ R) ∧
      (∀ s : ↥M ⧸ center ↥M, normalizerAct M ⟨e, heN⟩ s = s →
        normalizerAct M ⟨a, haN⟩ s * s⁻¹ ∈ R) := by
  classical
  set π : ↥M →* ↥M ⧸ center ↥M := QuotientGroup.mk' (center ↥M) with hπ
  set R : Subgroup (↥M ⧸ center ↥M) := ((O ⊓ M).subgroupOf M).map π with hR
  have hOI : Odd (Nat.card ↥(O ⊓ M)) := Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le inf_le_left)
  have hsub : Nat.card ↥((O ⊓ M).subgroupOf M) = Nat.card ↥(O ⊓ M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : O ⊓ M ≤ M)).toEquiv
  refine ⟨R, Odd.of_dvd_nat (hsub ▸ hOI) (Subgroup.card_map_dvd _ _), ?_, ?_⟩
  · intro s hs r hr
    obtain ⟨j, hj, hjs⟩ := lift_fixed hodd he2 heN hs
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    have hr₀' : ((r₀ : ↥M) : G) ∈ O ⊓ M := hr₀
    have hjC : (j : G) ∈ centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (j : G) * e = (e * (j : G) * e⁻¹) * e := by rw [hj]
        _ = e * j := by group
    refine ⟨j * r₀ * j⁻¹, ?_, by rw [← hjs]; simp [hπ]⟩
    show (((j * r₀ * j⁻¹ : ↥M)) : G) ∈ O ⊓ M
    exact ⟨hOnorm _ hjC _ hr₀'.1, (j * r₀ * j⁻¹).2⟩
  · intro s hs
    obtain ⟨j, hj, hjs⟩ := lift_fixed hodd he2 heN hs
    have hjC : (j : G) ∈ centralizer ({e} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (j : G) * e = (e * (j : G) * e⁻¹) * e := by rw [hj]
        _ = e * j := by group
    rw [← hjs, normalizerAct_apply_mk]
    refine ⟨conjOn M ⟨a, haN⟩ j * j⁻¹, ?_, by simp [hπ]⟩
    show ((conjOn M ⟨a, haN⟩ j * j⁻¹ : ↥M) : G) ∈ O ⊓ M
    refine ⟨?_, (conjOn M ⟨a, haN⟩ j * j⁻¹).2⟩
    have h1 := O.inv_mem (hZ _ hjC)
    have e1 : (j : G) * a * (j : G)⁻¹ * a⁻¹ = (j : G) * a * (j : G)⁻¹ * a⁻¹ := rfl
    have e2 : ((conjOn M ⟨a, haN⟩ j * j⁻¹ : ↥M) : G) = (j * a * j⁻¹ * a⁻¹)⁻¹ := by
      show a * (j : G) * a⁻¹ * (j : G)⁻¹ = ((j : G) * a * (j : G)⁻¹ * a⁻¹)⁻¹
      group
    rw [e2]
    exact h1

end Act

section Nbr

variable {G : Type} [Group G] [Finite G] {t : StatedLieTag} {p f : ℕ} {x y : G} {Iw Iv : Subgroup G}

theorem NbrData.exists_S_B4_at (hnd : NbrData G t p f x y Iw Iv) {w : ↥Iw} (hw2 : w * w = 1)
    (hw1 : (QuotientGroup.mk w : ↥Iw ⧸ center ↥Iw) ≠ 1) :
    ∃ S : Subgroup (↥Iw ⧸ center ↥Iw), InvDataB4 (p ^ f) (↥Iw ⧸ center ↥Iw) (QuotientGroup.mk w) S := by
  have hw2' : (QuotientGroup.mk w : ↥Iw ⧸ center ↥Iw) * QuotientGroup.mk w = 1 := by
    rw [← QuotientGroup.mk_mul, hw2]
    rfl
  rcases hnd.tag with rfl | rfl
  · exact exists_invDataB4_lin hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2
      (stated_of_lieModel_PSL hnd.model_w) hw2' hw1
  · obtain ⟨S, hS⟩ := (((libData_uni hnd.prime.1 hnd.prime.2.1 hnd.prime.2.2) _
      (stated_of_lieModel_PSU hnd.model_w)).1 _ hw2' hw1)
    exact ⟨S, hS.toB4⟩

end Nbr

end CFSG.GH74.Generic.S3
