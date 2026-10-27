module

import CFSG.GroupTheory.PermSylowTwo.SymCore
import CFSG.GroupTheory.PermutesConjSup
import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
import CFSG.GroupTheory.SylowInfNormal
public import CFSG.GroupTheory.SylowIntersectionControl.GomiComponents
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.QuasithinUnique CFSG.SignalizerFunctorTheorem.McBride
  CFSG.SignalizerFunctorTheorem.McBride.Near.Thm210

variable {G : Type} [Group G]

theorem le_normalizer_orbitClosure (Q U : Subgroup G) :
    U ≤ normalizer (orbitClosure Q U : Set G) := by
  have key : ∀ u ∈ U, orbitClosure Q U ≤
      (orbitClosure Q U).comap (MulAut.conj u).toMonoidHom := fun u hu =>
    orbitClosure_le fun v hv => by
      rw [← map_le_iff_le_comap, Subgroup.map_conj_map_conj]
      exact map_conj_le_orbitClosure Q (mul_mem hu hv)
  intro u hu
  refine mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · simpa using key u hu hx
  · simpa [mul_assoc] using key u⁻¹ (inv_mem hu) hx

private theorem map_conj_one (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp

private theorem map_conj_eq_self_of_le {A Q U : Subgroup G}
    (hUQ : U ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G)) {z : G} (hz : z ∈ U)
    (hzA : A.map (MulAut.conj z).toMonoidHom = A) : Q.map (MulAut.conj z).toMonoidHom = Q := by
  have hzN : z ∈ normalizer (A : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq]
    exact hzA
  exact mem_normalizer_iff_map_conj_eq.mp (hUQ (mem_inf.mpr ⟨hz, hzN⟩))

private def part (U A Q B : Subgroup G) : Subgroup G :=
  sSup {Y | ∃ u ∈ U, A.map (MulAut.conj u).toMonoidHom = B ∧ Y = Q.map (MulAut.conj u).toMonoidHom}

private theorem part_le {U A Q : Subgroup G} (hQA : Q ≤ A) (B : Subgroup G) : part U A Q B ≤ B :=
  sSup_le fun _ ⟨_, _, hB, hY⟩ => hY ▸ hB ▸ map_mono hQA

private theorem part_eq {U A Q : Subgroup G}
    (hUQ : U ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G)) {u : G} (hu : u ∈ U) :
    part U A Q (A.map (MulAut.conj u).toMonoidHom) = Q.map (MulAut.conj u).toMonoidHom :=
  le_antisymm (sSup_le fun _ ⟨_, hv, hB, hY⟩ => hY ▸
      (map_conj_eq_of_map_conj_eq hv hu (fun _ hz => map_conj_eq_self_of_le hUQ hz) hB).le)
    (le_sSup ⟨u, hu, rfl, rfl⟩)

private theorem orbitClosure_eq_sSup_part {S : Set (Subgroup G)} {U A Q : Subgroup G}
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S) :
    orbitClosure Q U = sSup {Y | ∃ B ∈ S, Y = part U A Q B} :=
  le_antisymm (orbitClosure_le fun u hu =>
      (le_sSup ⟨u, hu, rfl, rfl⟩ : Q.map (MulAut.conj u).toMonoidHom ≤
        part U A Q (A.map (MulAut.conj u).toMonoidHom)).trans (le_sSup ⟨_, hSG u A hA, rfl⟩))
    (sSup_le fun _ ⟨_, _, hY⟩ => hY ▸ sSup_le fun _ ⟨_, hu, _, hY'⟩ =>
      hY' ▸ map_conj_le_orbitClosure Q hu)

variable [Finite G] {S : Set (Subgroup G)} {N A Q U : Subgroup G}

theorem orbitClosure_inf_map_conj (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S) (hQA : Q ≤ A)
    (hUQ : U ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G)) {u : G} (hu : u ∈ U) :
    orbitClosure Q U ⊓ A.map (MulAut.conj u).toMonoidHom = Q.map (MulAut.conj u).toMonoidHom := by
  refine le_antisymm (fun x hx => ?_) (le_inf (map_conj_le_orbitClosure Q hu) (map_mono hQA))
  obtain ⟨hxP, hxB⟩ := mem_inf.mp hx
  rw [orbitClosure_eq_sSup_part hSG hA] at hxP
  obtain ⟨hxN, hc⟩ := (mem_sSup_image_iff hN fun B _ => part_le hQA B).mp hxP
  have hB := hSG u A hA
  have h := hc _ hB
  rwa [hN.coord_of_mem hB hxB, part_eq hUQ hu] at h

theorem orbitClosure_eq_sSup_inf (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S) (hQA : Q ≤ A) :
    orbitClosure Q U ≤ N ∧ orbitClosure Q U = sSup {Y | ∃ B ∈ S, Y = orbitClosure Q U ⊓ B} := by
  have h := (le_sSup_image_iff hN (T := part U A Q) fun B _ => part_le hQA B).mp
    (orbitClosure_eq_sSup_part hSG hA).le
  refine ⟨h.1, eq_sSup_inf hN h.1 fun B hB => (h.2 B hB).trans ?_⟩
  rw [orbitClosure_eq_sSup_part hSG hA]
  exact le_sSup ⟨B, hB, rfl⟩

omit [Finite G] in
private theorem mem_map_conj_of_mem_normalizer (hQ : A ⊓ normalizer (Q : Set G) ≤ Q) {u c : G}
    (hcA : c ∈ A.map (MulAut.conj u).toMonoidHom)
    (hcQ : c ∈ normalizer ((Q.map (MulAut.conj u).toMonoidHom : Subgroup G) : Set G)) :
    c ∈ Q.map (MulAut.conj u).toMonoidHom := by
  obtain ⟨a, ha, rfl⟩ := hcA
  refine ⟨a, hQ (mem_inf.mpr ⟨ha, ?_⟩), rfl⟩
  rw [mem_normalizer_iff_map_conj_eq] at hcQ ⊢
  change (Q.map (MulAut.conj u).toMonoidHom).map (MulAut.conj (u * a * u⁻¹)).toMonoidHom =
    Q.map (MulAut.conj u).toMonoidHom at hcQ
  change Q.map (MulAut.conj a).toMonoidHom = Q
  have h := congrArg (Subgroup.map (MulAut.conj u⁻¹).toMonoidHom) hcQ
  rwa [Subgroup.map_conj_map_conj, Subgroup.map_conj_map_conj, Subgroup.map_conj_map_conj,
    show u⁻¹ * (u * a * u⁻¹) * u = a by group, inv_mul_cancel, map_conj_one] at h

private theorem conj_eq_coord_conj (hN : IsDirectProduct S N) {B : Subgroup G} (hB : B ∈ S)
    {n : G} (hn : n ∈ N) {q : G} (hq : q ∈ B) :
    n * q * n⁻¹ = (hN.coord hB ⟨n, hn⟩ : G) * q * (hN.coord hB ⟨n, hn⟩ : G)⁻¹ := by
  have hnq : n * q * n⁻¹ ∈ B := (mem_normalizer_iff.mp (hN.le_normalizer hB hn) q).mp hq
  have h1 := hN.coord_of_mem hB hnq
  have h3 : (⟨n * q * n⁻¹, hN.le hB hnq⟩ : N) = ⟨n, hn⟩ * ⟨q, hN.le hB hq⟩ * (⟨n, hn⟩ : N)⁻¹ :=
    rfl
  rw [h3, map_mul, map_mul, map_inv] at h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hN.coord_of_mem hB hq] at h1
  exact h1.symm

theorem inf_normalizer_orbitClosure (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S)
    (hU : ∀ B ∈ S, ∃ u ∈ U, A.map (MulAut.conj u).toMonoidHom = B) (hQA : Q ≤ A)
    (hQ : A ⊓ normalizer (Q : Set G) ≤ Q)
    (hUQ : U ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G)) :
    N ⊓ normalizer (orbitClosure Q U : Set G) = orbitClosure Q U := by
  refine le_antisymm (fun n hn => ?_)
    (le_inf (orbitClosure_eq_sSup_inf hN hSG hA hQA).1 le_normalizer)
  obtain ⟨hnN, hnP⟩ := mem_inf.mp hn
  refine hN.mem_of_coord_mem hnN fun B hB => ?_
  obtain ⟨u, hu, rfl⟩ := hU B hB
  have hPB := orbitClosure_inf_map_conj hN hSG hA hQA hUQ hu
  have key : ∀ (m : G) (hm : m ∈ N), m ∈ normalizer (orbitClosure Q U : Set G) →
      ∀ q ∈ Q.map (MulAut.conj u).toMonoidHom,
        ((hN.coord hB ⟨m, hm⟩ : _) : G) * q * ((hN.coord hB ⟨m, hm⟩ : _) : G)⁻¹ ∈
          Q.map (MulAut.conj u).toMonoidHom := by
    intro m hm hmP q hq
    have hqB : q ∈ A.map (MulAut.conj u).toMonoidHom := map_mono hQA hq
    rw [← conj_eq_coord_conj hN hB hm hqB, ← hPB]
    exact mem_inf.mpr ⟨(mem_normalizer_iff.mp hmP q).mp (map_conj_le_orbitClosure Q hu hq),
      (mem_normalizer_iff.mp (hN.le_normalizer hB hm) q).mp hqB⟩
  refine mem_inf.mp (hPB.ge (mem_map_conj_of_mem_normalizer hQ (hN.coord hB ⟨n, hnN⟩).2 ?_)) |>.1
  refine mem_normalizer_iff.mpr fun q => ⟨key n hnN hnP q, fun hq => ?_⟩
  have h := key n⁻¹ (inv_mem hnN) (inv_mem hnP) _ hq
  have hinv : ((hN.coord hB ⟨n⁻¹, inv_mem hnN⟩ : _) : G) =
      ((hN.coord hB ⟨n, hnN⟩ : _) : G)⁻¹ := by
    rw [show (⟨n⁻¹, inv_mem hnN⟩ : N) = (⟨n, hnN⟩ : N)⁻¹ from rfl, map_inv]
    rfl
  rwa [hinv, show ∀ x y : G, x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y from fun x y => by group] at h

private theorem sylow_sup_eq_top_of_isPGroup [N.Normal] (hGN : IsPGroup 2 (G ⧸ N))
    (U : Sylow 2 G) : (U : Subgroup G) ⊔ N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : (U : Subgroup G).map (QuotientGroup.mk' N) = ⊤ := by
    change ((U.mapSurjective (QuotientGroup.mk'_surjective N) : Sylow 2 (G ⧸ N)) :
      Subgroup (G ⧸ N)) = ⊤
    exact ((U.mapSurjective (QuotientGroup.mk'_surjective N)).is_maximal'
      (hGN.to_subgroup ⊤) le_top).symm
  have h := comap_map_eq (QuotientGroup.mk' N) (U : Subgroup G)
  rw [hQ, comap_top, QuotientGroup.ker_mk'] at h
  exact h.symm

theorem exists_mem_sylow_map_conj_eq [N.Normal] (hGN : IsPGroup 2 (G ⧸ N)) (U : Sylow 2 G)
    (hNA : N ≤ normalizer (A : Set G)) {B : Subgroup G}
    (hB : ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B) :
    ∃ u ∈ (U : Subgroup G), A.map (MulAut.conj u).toMonoidHom = B := by
  obtain ⟨g, rfl⟩ := hB
  have hg : g ∈ ((U : Subgroup G) ⊔ N : Subgroup G) := by
    rw [sylow_sup_eq_top_of_isPGroup hGN U]
    exact mem_top g
  rw [← SetLike.mem_coe, mul_normal] at hg
  obtain ⟨u, hu, z, hz, rfl⟩ := hg
  refine ⟨u, hu, ?_⟩
  have hzA := mem_normalizer_iff_map_conj_eq.mp (hNA hz)
  change A.map (MulAut.conj z).toMonoidHom = A at hzA
  rw [← Subgroup.map_conj_map_conj, hzA]

theorem isSylowTwoOf_sylow_inf_normalizer [N.Normal] (hGN : IsPGroup 2 (G ⧸ N)) (U : Sylow 2 G)
    (hNA : N ≤ normalizer (A : Set G)) :
    IsSylowTwoOf ((U : Subgroup G) ⊓ normalizer (A : Set G)) (normalizer (A : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := (U : Subgroup G) ⊓ normalizer (A : Set G)
  refine ⟨inf_le_right, U.isPGroup'.to_le inf_le_left, ?_⟩
  have hUN : IsSylowTwoOf (N ⊓ U) N := by
    refine isSylowTwoOf_inf_of_normal ⟨le_top, U.isPGroup', ?_⟩ le_top ?_
    · change ¬ 2 ∣ (U : Subgroup G).relIndex ⊤
      rw [relIndex_top_right]
      exact U.not_dvd_index
    · exact fun g _ => by rw [normalizer_eq_top]; exact mem_top g
  have hY : X ⊔ N = normalizer (A : Set G) := by
    refine le_antisymm (sup_le inf_le_right hNA) fun y hy => ?_
    have hy' : y ∈ ((U : Subgroup G) ⊔ N : Subgroup G) := by
      rw [sylow_sup_eq_top_of_isPGroup hGN U]
      exact mem_top y
    rw [← SetLike.mem_coe, mul_normal] at hy'
    obtain ⟨u, hu, z, hz, rfl⟩ := hy'
    have huA : u ∈ normalizer (A : Set G) := by
      simpa using mul_mem hy (inv_mem (hNA hz))
    exact mul_mem (mem_sup_left (mem_inf.mpr ⟨hu, huA⟩)) (mem_sup_right hz)
  have hXN : X ⊓ N = N ⊓ U := by
    change ((U : Subgroup G) ⊓ normalizer (A : Set G)) ⊓ N = N ⊓ U
    rw [inf_assoc, inf_eq_right.mpr hNA, inf_comm]
  have h := (relIndex_sup_eq_relIndex_inf_of_le_normalizer (H := X) (K := N)
    (by rw [normalizer_eq_top]; exact le_top)).1
  rw [hY, hXN] at h
  change ¬ 2 ∣ X.relIndex (normalizer (A : Set G))
  rw [h]
  exact hUN.2.2

omit [Finite G] in
private theorem map_conj_eq_of_mem_normalizer {K : Subgroup G} {g : G}
    (hg : g ∈ normalizer (K : Set G)) : K.map (MulAut.conj g).toMonoidHom = K :=
  mem_normalizer_iff_map_conj_eq.mp hg

omit [Finite G] in
private theorem map_conj_inf_of_map_conj_eq (K B : Subgroup G) {g : G}
    (hg : B.map (MulAut.conj g).toMonoidHom = B) :
    (K ⊓ B).map (MulAut.conj g).toMonoidHom = K.map (MulAut.conj g).toMonoidHom ⊓ B := by
  rw [map_inf_eq _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective, hg]

omit [Finite G] in
private theorem map_conj_orbitClosure_le {Q U X : Subgroup G} {y : G}
    (h : ∀ u ∈ U, Q.map (MulAut.conj (y * u)).toMonoidHom ≤ X) :
    (orbitClosure Q U).map (MulAut.conj y).toMonoidHom ≤ X := by
  rw [map_le_iff_le_comap]
  exact orbitClosure_le fun u hu => by
    rw [← map_le_iff_le_comap, Subgroup.map_conj_map_conj]
    exact h u hu

omit [Finite G] in
private theorem index_normalizer_map_conj (P : Subgroup G) (g : G) :
    (normalizer ((P.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).index =
      (normalizer (P : Set G)).index := by
  rw [← map_equiv_normalizer_eq,
    index_map_of_bijective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).bijective]

private theorem map_conj_eq_map_conj_coord (hN : IsDirectProduct S N) {B : Subgroup G}
    (hB : B ∈ S) {n : G} (hn : n ∈ N) {R : Subgroup G} (hR : R ≤ B) :
    R.map (MulAut.conj n).toMonoidHom =
      R.map (MulAut.conj (hN.coord hB ⟨n, hn⟩ : G)).toMonoidHom := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact ⟨fun ⟨r, hr, hx⟩ => ⟨r, hr, (conj_eq_coord_conj hN hB hn (hR hr)).symm.trans hx⟩,
    fun ⟨r, hr, hx⟩ => ⟨r, hr, (conj_eq_coord_conj hN hB hn (hR hr)).trans hx⟩⟩

private theorem exists_mem_coord_eq (hN : IsDirectProduct S N) (f : Subgroup G → G)
    (hf : ∀ B ∈ S, f B ∈ B) :
    ∃ c : G, ∃ hc : c ∈ N, ∀ (B : Subgroup G) (hB : B ∈ S), (hN.coord hB ⟨c, hc⟩ : G) = f B :=
  ⟨hN.equiv fun B => ⟨f B, hf B B.2⟩, (hN.equiv _).2, fun _ hB =>
    congrArg Subtype.val (hN.coord_equiv hB fun B => ⟨f B, hf B B.2⟩)⟩

private theorem exists_le_normalizer_map_conj [N.Normal] (hGN : IsPGroup 2 (G ⧸ N))
    (U : Sylow 2 G) {K H : Subgroup G} (hUK : (U : Subgroup G) ≤ normalizer (K : Set G))
    (hH : IsPGroup 2 H) :
    ∃ x ∈ N, H ≤ normalizer ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hHT⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U T
  have hgT : (U : Subgroup G).map (MulAut.conj g).toMonoidHom = T := by
    rw [← hg]
    rfl
  have hg' : g⁻¹ ∈ ((U : Subgroup G) ⊔ N : Subgroup G) := by
    rw [sylow_sup_eq_top_of_isPGroup hGN U]
    exact mem_top _
  rw [← SetLike.mem_coe, mul_normal] at hg'
  obtain ⟨s, hs, n, hn, hsn⟩ := hg'
  change s * n = g⁻¹ at hsn
  have hU : (U : Subgroup G).map (MulAut.conj s⁻¹).toMonoidHom = U :=
    map_conj_eq_of_mem_normalizer (le_normalizer (inv_mem hs))
  refine ⟨n⁻¹, inv_mem hn, ?_⟩
  calc H ≤ T := hHT
    _ = (U : Subgroup G).map (MulAut.conj (n⁻¹ * s⁻¹)).toMonoidHom := by
        rw [← mul_inv_rev, hsn, inv_inv, hgT]
    _ = (U : Subgroup G).map (MulAut.conj n⁻¹).toMonoidHom := by
        rw [← Subgroup.map_conj_map_conj (U : Subgroup G) s⁻¹ n⁻¹, hU]
    _ ≤ (normalizer (K : Set G)).map (MulAut.conj n⁻¹).toMonoidHom := map_mono hUK
    _ = normalizer ((K.map (MulAut.conj n⁻¹).toMonoidHom : Subgroup G) : Set G) :=
        map_equiv_normalizer_eq K (MulAut.conj n⁻¹)

private theorem exists_mem_map_conj_inf_eq (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S) (hQA : Q ≤ A)
    {H P₀ : Subgroup G} (hHQ : H ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G))
    (hHP : H ≤ normalizer (P₀ : Set G)) {x : G} (hx : x ∈ N)
    (hPA : P₀ ⊓ A = Q.map (MulAut.conj x).toMonoidHom) :
    ∃ c ∈ N, (∀ h ∈ H, P₀.map (MulAut.conj c).toMonoidHom ⊓ A.map (MulAut.conj h).toMonoidHom =
        Q.map (MulAut.conj h).toMonoidHom) ∧
      ∀ B ∈ S, (¬ ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom = B) →
        P₀.map (MulAut.conj c).toMonoidHom ⊓ B = P₀ ⊓ B := by
  obtain ⟨a, ha, hPA'⟩ : ∃ a ∈ A, P₀ ⊓ A = Q.map (MulAut.conj a).toMonoidHom :=
    ⟨_, (hN.coord hA ⟨x, hx⟩).2, hPA.trans (map_conj_eq_map_conj_coord hN hA hx hQA)⟩
  have hf : ∀ B ∈ S, ∃ y ∈ B, (∀ h ∈ H, A.map (MulAut.conj h).toMonoidHom = B →
      (P₀ ⊓ B).map (MulAut.conj y).toMonoidHom = Q.map (MulAut.conj h).toMonoidHom) ∧
      ((¬ ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom = B) → y = 1) := by
    intro B _
    by_cases hex : ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom = B
    · obtain ⟨k, hk, rfl⟩ := hex
      refine ⟨k * a⁻¹ * k⁻¹, ⟨a⁻¹, inv_mem ha, rfl⟩, fun h hh hkh => ?_,
        fun hn => (hn ⟨k, hk, rfl⟩).elim⟩
      have hPk : P₀ ⊓ A.map (MulAut.conj k).toMonoidHom =
          (P₀ ⊓ A).map (MulAut.conj k).toMonoidHom := by
        rw [map_inf_eq _ _ (MulAut.conj k).toMonoidHom (MulAut.conj k).injective,
          map_conj_eq_of_mem_normalizer (hHP hk)]
      rw [hPk, hPA', Subgroup.map_conj_map_conj Q a k,
        Subgroup.map_conj_map_conj Q (k * a) (k * a⁻¹ * k⁻¹),
        show k * a⁻¹ * k⁻¹ * (k * a) = k by group]
      exact map_conj_eq_of_map_conj_eq hk hh (fun _ hz => map_conj_eq_self_of_le hHQ hz) hkh.symm
    · exact ⟨1, one_mem B, fun h hh hB' => (hex ⟨h, hh, hB'⟩).elim, fun _ => rfl⟩
  choose! f hfB hforb hfoff using hf
  obtain ⟨c, hc, hcf⟩ := exists_mem_coord_eq hN f hfB
  have hpart : ∀ B ∈ S, P₀.map (MulAut.conj c).toMonoidHom ⊓ B =
      (P₀ ⊓ B).map (MulAut.conj (f B)).toMonoidHom := fun B hB => by
    rw [← map_conj_inf_of_map_conj_eq P₀ B
        (map_conj_eq_of_mem_normalizer (hN.le_normalizer hB hc)),
      map_conj_eq_map_conj_coord hN hB hc (inf_le_right : P₀ ⊓ B ≤ B), hcf B hB]
  refine ⟨c, hc, fun h hh => ?_, fun B hB hn => ?_⟩
  · rw [hpart _ (hSG h A hA)]
    exact hforb _ (hSG h A hA) h hh rfl
  · rw [hpart B hB, hfoff B hB hn, map_conj_one]

omit [Finite G] in
private theorem le_normalizer_of_inf_eq {H P₀ P' : Subgroup G}
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S)
    (hHP : H ≤ normalizer (P₀ : Set G)) (hP' : P' ≤ sSup {Y | ∃ B ∈ S, Y = P' ⊓ B})
    (horb : ∀ h ∈ H, P' ⊓ A.map (MulAut.conj h).toMonoidHom = Q.map (MulAut.conj h).toMonoidHom)
    (hoff : ∀ B ∈ S, (¬ ∃ h ∈ H, A.map (MulAut.conj h).toMonoidHom = B) → P' ⊓ B = P₀ ⊓ B) :
    H ≤ normalizer (P' : Set G) := by
  have key : ∀ h ∈ H, P'.map (MulAut.conj h).toMonoidHom ≤ P' := by
    intro h hh
    rw [map_le_iff_le_comap]
    refine hP'.trans (sSup_le ?_)
    rintro _ ⟨B, hB, rfl⟩
    rw [← map_le_iff_le_comap]
    by_cases hex : ∃ k ∈ H, A.map (MulAut.conj k).toMonoidHom = B
    · obtain ⟨k, hk, rfl⟩ := hex
      rw [horb k hk, Subgroup.map_conj_map_conj, ← horb (h * k) (mul_mem hh hk)]
      exact inf_le_left
    have hB' : ¬ ∃ k ∈ H,
        A.map (MulAut.conj k).toMonoidHom = B.map (MulAut.conj h).toMonoidHom := by
      rintro ⟨k, hk, hkB⟩
      refine hex ⟨h⁻¹ * k, mul_mem (inv_mem hh) hk, ?_⟩
      rw [← Subgroup.map_conj_map_conj A k h⁻¹, hkB, Subgroup.map_conj_map_conj, inv_mul_cancel,
        map_conj_one]
    calc (P' ⊓ B).map (MulAut.conj h).toMonoidHom
        = (P₀ ⊓ B).map (MulAut.conj h).toMonoidHom := by rw [hoff B hB hex]
      _ = P₀ ⊓ B.map (MulAut.conj h).toMonoidHom := by
        rw [map_inf_eq _ _ (MulAut.conj h).toMonoidHom (MulAut.conj h).injective,
          map_conj_eq_of_mem_normalizer (hHP hh)]
      _ = P' ⊓ B.map (MulAut.conj h).toMonoidHom := (hoff _ (hSG h B hB) hB').symm
      _ ≤ P' := inf_le_left
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (key h hh) ?_
  have h' := map_mono (f := (MulAut.conj h).toMonoidHom) (key h⁻¹ (inv_mem hh))
  rwa [Subgroup.map_conj_map_conj, mul_inv_cancel, map_conj_one] at h'

private theorem map_conj_orbitClosure_props [N.Normal] (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S)
    (hU : ∀ B ∈ S, ∃ u ∈ U, A.map (MulAut.conj u).toMonoidHom = B) (hQA : Q ≤ A)
    (hQ : A ⊓ normalizer (Q : Set G) ≤ Q)
    (hUQ : U ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G)) {y : G} (hy : y ∈ N) :
    (∀ u ∈ U, (orbitClosure Q U).map (MulAut.conj y).toMonoidHom ⊓
        A.map (MulAut.conj u).toMonoidHom = Q.map (MulAut.conj (y * u)).toMonoidHom) ∧
      (orbitClosure Q U).map (MulAut.conj y).toMonoidHom ≤
        sSup {Y | ∃ B ∈ S, Y = (orbitClosure Q U).map (MulAut.conj y).toMonoidHom ⊓ B} ∧
      N ⊓ normalizer (((orbitClosure Q U).map (MulAut.conj y).toMonoidHom : Subgroup G) :
        Set G) = (orbitClosure Q U).map (MulAut.conj y).toMonoidHom := by
  have h1 : ∀ u ∈ U, (orbitClosure Q U).map (MulAut.conj y).toMonoidHom ⊓
      A.map (MulAut.conj u).toMonoidHom = Q.map (MulAut.conj (y * u)).toMonoidHom := by
    intro u hu
    rw [← map_conj_inf_of_map_conj_eq (orbitClosure Q U) _
        (map_conj_eq_of_mem_normalizer (hN.le_normalizer (hSG u A hA) hy)),
      orbitClosure_inf_map_conj hN hSG hA hQA hUQ hu, Subgroup.map_conj_map_conj]
  refine ⟨h1, map_conj_orbitClosure_le fun u hu => le_sSup ⟨_, hSG u A hA, (h1 u hu).symm⟩, ?_⟩
  have hNy : N.map (MulAut.conj y).toMonoidHom = N :=
    map_conj_eq_of_mem_normalizer (by rw [normalizer_eq_top]; exact mem_top y)
  calc N ⊓ normalizer (((orbitClosure Q U).map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G)
      = (N ⊓ normalizer (orbitClosure Q U : Set G)).map (MulAut.conj y).toMonoidHom := by
        rw [map_inf_eq _ _ (MulAut.conj y).toMonoidHom (MulAut.conj y).injective, hNy,
          map_equiv_normalizer_eq]
    _ = (orbitClosure Q U).map (MulAut.conj y).toMonoidHom := by
        rw [inf_normalizer_orbitClosure hN hSG hA hU hQA hQ hUQ]

omit [Finite G] in
private theorem exists_normalizer_of_props (hN : IsDirectProduct S N) (hA : A ∈ S)
    {H P : Subgroup G} (hodd : Odd (normalizer (P : Set G)).index)
    (hHP : H ≤ normalizer (P : Set G)) (hPN : N ⊓ normalizer (P : Set G) = P)
    (hPle : P ≤ sSup {Y | ∃ B ∈ S, Y = P ⊓ B}) (hPA : P ⊓ A = Q)
    (hPB : ∀ B ∈ S, ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B ∧
      P ⊓ B = Q.map (MulAut.conj g).toMonoidHom) :
    ∃ M : Subgroup G, Odd M.index ∧ H ≤ M ∧ M ⊓ A = Q ∧ (Q ≠ A → M ≠ ⊤) ∧
      M ⊓ N = sSup {Y | ∃ B ∈ S, Y = M ⊓ B} ∧
      ∀ B ∈ S, ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B ∧
        M ⊓ B = Q.map (MulAut.conj g).toMonoidHom := by
  have hMB : ∀ B ∈ S, normalizer (P : Set G) ⊓ B = P ⊓ B := fun B hB =>
    calc normalizer (P : Set G) ⊓ B = (N ⊓ normalizer (P : Set G)) ⊓ B := by
          rw [inf_comm N, inf_assoc, inf_eq_right.mpr (hN.le hB)]
      _ = P ⊓ B := by rw [hPN]
  have hMA : normalizer (P : Set G) ⊓ A = Q := (hMB A hA).trans hPA
  refine ⟨normalizer (P : Set G), hodd, hHP, hMA, fun hne htop => hne ?_, ?_, fun B hB => ?_⟩
  · rw [htop, top_inf_eq] at hMA
    exact hMA.symm
  · rw [inf_comm _ N, hPN]
    refine le_antisymm (hPle.trans (sSup_le ?_)) (sSup_le ?_)
    · rintro _ ⟨B, hB, rfl⟩
      exact le_sSup ⟨B, hB, (hMB B hB).symm⟩
    · rintro _ ⟨B, hB, rfl⟩
      exact (hMB B hB).le.trans inf_le_left
  · obtain ⟨g, hg, hPg⟩ := hPB B hB
    exact ⟨g, hg, (hMB B hB).trans hPg⟩

theorem exists_odd_index_inf_eq [N.Normal] (hN : IsDirectProduct S N)
    (hSG : ∀ g : G, ∀ J ∈ S, J.map (MulAut.conj g).toMonoidHom ∈ S) (hA : A ∈ S)
    (hS : ∀ B ∈ S, ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B) (hGN : IsPGroup 2 (G ⧸ N))
    {H : Subgroup G} (hH : IsPGroup 2 H) (hQA : Q ≤ A) (hQ : A ⊓ normalizer (Q : Set G) ≤ Q)
    (hTQ : ∃ T : Subgroup G, IsSylowTwoOf T (normalizer (A : Set G)) ∧
      T ≤ normalizer (Q : Set G))
    (hHQ : H ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G)) :
    ∃ M : Subgroup G, Odd M.index ∧ H ≤ M ∧ M ⊓ A = Q ∧ (Q ≠ A → M ≠ ⊤) ∧
      M ⊓ N = sSup {Y | ∃ B ∈ S, Y = M ⊓ B} ∧
      ∀ B ∈ S, ∃ g : G, A.map (MulAut.conj g).toMonoidHom = B ∧
        M ⊓ B = Q.map (MulAut.conj g).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hTQ⟩ := hTQ
  obtain ⟨R, hTR⟩ := hT.2.1.exists_le_sylow
  have hRQ : (R : Subgroup G) ⊓ normalizer (A : Set G) ≤ normalizer (Q : Set G) :=
    (PermSylowTwo.le_of_isSylowTwoOf_of_isPGroup hT (le_inf hTR hT.1) inf_le_right
      (R.isPGroup'.to_le inf_le_left)).trans hTQ
  have hRS : ∀ B ∈ S, ∃ u ∈ (R : Subgroup G), A.map (MulAut.conj u).toMonoidHom = B :=
    fun B hB => exists_mem_sylow_map_conj_eq hGN R (hN.le_normalizer hA) (hS B hB)
  obtain ⟨x, hx, hHx⟩ :=
    exists_le_normalizer_map_conj hGN R (le_normalizer_orbitClosure Q R) hH
  have hxA := (map_conj_orbitClosure_props hN hSG hA hRS hQA hQ hRQ hx).1 1 (one_mem _)
  rw [map_conj_one, mul_one] at hxA
  obtain ⟨c, hc, horb, hoff⟩ := exists_mem_map_conj_inf_eq hN hSG hA hQA hHQ hHx hx hxA
  rw [Subgroup.map_conj_map_conj (orbitClosure Q (R : Subgroup G)) x c] at horb hoff
  obtain ⟨hPu, hPle, hPN⟩ :=
    map_conj_orbitClosure_props hN hSG hA hRS hQA hQ hRQ (mul_mem hc hx)
  refine exists_normalizer_of_props hN hA ?_ (le_normalizer_of_inf_eq hSG hHx hPle horb hoff)
    hPN hPle ?_ fun B hB => ?_
  · rw [index_normalizer_map_conj]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h => R.not_dvd_index
      (h.trans (index_dvd_of_le (le_normalizer_orbitClosure Q R))))
  · have h := horb 1 (one_mem H)
    rwa [map_conj_one, map_conj_one] at h
  · obtain ⟨u, hu, rfl⟩ := hRS B hB
    refine ⟨c * x * u, ?_, hPu u hu⟩
    rw [← Subgroup.map_conj_map_conj A u (c * x)]
    exact map_conj_eq_of_mem_normalizer (hN.le_normalizer hB (mul_mem hc hx))

end CFSG.GroupTheory
