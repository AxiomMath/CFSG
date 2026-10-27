module

public import CFSG.LieType.Steinberg.Bruhat

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
open scoped commutatorElement Pointwise

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

theorem coe_posUnipotent_eq_mul_rootGroup (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    (posUnipotent D : Set K) = (posUnipotentExcept D i : Set K) *
      (D.rootGroup (Pi.single i 1) : Set K) := by
  rw [posUnipotent_eq_sup hext i]
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (rootGroup_single_le_normalizer hext i)

theorem coe_posUnipotent_eq_rootGroup_mul (hext : SteinbergExtras D n H) (i : Fin D.rank) :
    (posUnipotent D : Set K) = (D.rootGroup (Pi.single i 1) : Set K) *
      (posUnipotentExcept D i : Set K) := by
  rw [posUnipotent_eq_sup hext i, sup_comm]
  exact Subgroup.coe_mul_of_left_le_normalizer_right _ _
    (rootGroup_single_le_normalizer hext i)

theorem inv_conj_n_mem_rootGroup_neg (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (i : Fin D.rank) {x : K} (hx : x ∈ D.rootGroup (Pi.single i 1)) :
    (n i)⁻¹ * x * n i ∈ D.rootGroup (-Pi.single i 1) := by
  have h := (actsAs_n hct i).inv_conj_mem ((Φ).single_mem i) hx
  rwa [(cs).inv_simple, weylAction_simple_single] at h

theorem conj_n_mem_rootGroup_neg (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (i : Fin D.rank) {x : K} (hx : x ∈ D.rootGroup (Pi.single i 1)) :
    n i * x * (n i)⁻¹ ∈ D.rootGroup (-Pi.single i 1) := by
  have h := (actsAs_n hct i).conj_mem ((Φ).single_mem i) hx
  rwa [weylAction_simple_single] at h

theorem notMem_borel_of_conj (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hBU : BruhatExtras D H) (i : Fin D.rank) {x : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) (hx1 : x ≠ 1) :
    n i * x * n i ∉ borel D H := by
  intro hB
  have hsq : n i * n i ∈ borel D H :=
    iSup_le_borel (le_iSup H i (by rw [← pow_two]; exact hct.sq_mem i))
  have hmem : n i * x * (n i)⁻¹ ∈ borel D H ⊓ negUnipotent D := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have e : n i * x * (n i)⁻¹ = (n i * x * n i) * (n i * n i)⁻¹ := by group
      rw [e]
      exact mul_mem hB (inv_mem hsq)
    · exact rootGroup_le_negUnipotent ((Φ).neg_mem _ ((Φ).single_mem i))
        (by rw [ht_neg, ht_single]; norm_num) (conj_n_mem_rootGroup_neg hct i hx)
  rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at hmem
  apply hx1
  have hinj : n i * x * (n i)⁻¹ = n i * (1 : K) * (n i)⁻¹ := by rw [hmem]; group
  exact mul_left_cancel (mul_right_cancel hinj)

structure RankOneData (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (i : Fin D.rank) (x : K) where
  h : K
  h_mem : h ∈ H i
  u : K
  u_mem : u ∈ D.rootGroup (Pi.single i 1)
  v : K
  v_mem : v ∈ D.rootGroup (Pi.single i 1)
  eq : n i * x * n i = u * n i * h * v

theorem exists_rankOne_data (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (i : Fin D.rank) {x : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1) ∧ x ≠ 1) :
    Nonempty (RankOneData hct hext hBU i x) := by
  have hg : n i * x * n i ∈ rankOne D.rootGroup i :=
    mul_mem (mul_mem (hct.n_mem i) (Subgroup.mem_sup_left hx.1)) (hct.n_mem i)
  rcases hext.rankOne_bruhat i _ hg with ⟨h, hh, u, hu, he⟩ | ⟨u, hu, h, hh, v, hv, he⟩
  · exact absurd (he ▸ mul_mem (iSup_le_borel (le_iSup H i hh))
      (rootGroup_le_borel ((Φ).single_mem i) (ht_single_pos i) hu))
      (notMem_borel_of_conj hct hBU i hx.1 hx.2)
  · exact ⟨⟨h, hh, u, hu, v, hv, he⟩⟩

open _root_.Classical in
@[expose] noncomputable def rankOnePhi (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (i : Fin D.rank) (x : K) : K :=
  if hx : x ∈ D.rootGroup (Pi.single i 1) ∧ x ≠ 1 then
    (Classical.choice (exists_rankOne_data hct hext hBU i hx)).h
  else 1

open _root_.Classical in
@[expose] noncomputable def rankOnePsi (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (i : Fin D.rank) (x : K) : K :=
  rankOnePhi hct hext hBU i x

theorem rankOnePhi_mem (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (i : Fin D.rank) {x : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) (hx1 : x ≠ 1) :
    rankOnePhi hct hext hBU i x ∈ H i := by
  unfold rankOnePhi
  rw [dif_pos ⟨hx, hx1⟩]
  exact (Classical.choice (exists_rankOne_data hct hext hBU i ⟨hx, hx1⟩)).h_mem

theorem rankOnePsi_mem (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (i : Fin D.rank) {x : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) (hx1 : x ≠ 1) :
    rankOnePsi hct hext hBU i x ∈ H i :=
  rankOnePhi_mem hct hext hBU i hx hx1

theorem rankOnePhi_spec (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (i : Fin D.rank) {x : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) (hx1 : x ≠ 1) :
    ∃ l ∈ negUnipotent D, ∃ u ∈ posUnipotent D,
      x * n i = l * rankOnePhi hct hext hBU i x * u := by
  unfold rankOnePhi
  rw [dif_pos ⟨hx, hx1⟩]
  let d := Classical.choice (exists_rankOne_data hct hext hBU i ⟨hx, hx1⟩)
  refine ⟨(n i)⁻¹ * d.u * n i, ?_, d.v,
    rootGroup_le_posUnipotent ((Φ).single_mem i) (ht_single_pos i) d.v_mem, ?_⟩
  · exact rootGroup_le_negUnipotent ((Φ).neg_mem _ ((Φ).single_mem i))
      (by rw [ht_neg, ht_single]; norm_num) (inv_conj_n_mem_rootGroup_neg hct i d.u_mem)
  · calc x * n i = (n i)⁻¹ * (n i * x * n i) := by group
      _ = (n i)⁻¹ * (d.u * n i * d.h * d.v) := by rw [d.eq]
      _ = (n i)⁻¹ * d.u * n i * d.h * d.v := by group

theorem rankOnePsi_spec (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (i : Fin D.rank) {x : K}
    (hx : x ∈ D.rootGroup (Pi.single i 1)) (hx1 : x ≠ 1) :
    ∃ a ∈ D.rootGroup (Pi.single i 1), ∃ u ∈ posUnipotent D,
      n i * x * n i = a * n i * rankOnePsi hct hext hBU i x * u := by
  unfold rankOnePsi rankOnePhi
  rw [dif_pos ⟨hx, hx1⟩]
  let d := Classical.choice (exists_rankOne_data hct hext hBU i ⟨hx, hx1⟩)
  exact ⟨d.u, d.u_mem, d.v,
    rootGroup_le_posUnipotent ((Φ).single_mem i) (ht_single_pos i) d.v_mem, d.eq⟩

theorem bruhatY_of_rankOne (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (i : Fin D.rank) {y : K}
    (hy : y ∈ D.rootGroup (-Pi.single i 1)) (hy1 : y ≠ 1) :
    ∃ h ∈ ⨆ j, H j, ∃ a ∈ D.rootGroup (Pi.single i 1),
      ∃ c ∈ D.rootGroup (Pi.single i 1), y = a * (h * n i) * c := by
  have hg : y ∈ rankOne D.rootGroup i := Subgroup.mem_sup_right hy
  rcases hext.rankOne_bruhat i _ hg with ⟨h, hh, u, hu, he⟩ | ⟨u, hu, h, hh, v, hv, he⟩
  · exfalso
    apply hy1
    have hB : y ∈ borel D H := he ▸ mul_mem (iSup_le_borel (le_iSup H i hh))
      (rootGroup_le_borel ((Φ).single_mem i) (ht_single_pos i) hu)
    have hL : y ∈ negUnipotent D := rootGroup_le_negUnipotent
      ((Φ).neg_mem _ ((Φ).single_mem i)) (by rw [ht_neg, ht_single]; norm_num) hy
    have hmem := Subgroup.mem_inf.2 ⟨hB, hL⟩
    rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at hmem
    exact hmem
  · refine ⟨n i * h * (n i)⁻¹, conj_n_mem_iSup hct i (le_iSup H i hh), u, hu, v, hv, ?_⟩
    rw [he]
    group

end CFSG.LieType.Steinberg
