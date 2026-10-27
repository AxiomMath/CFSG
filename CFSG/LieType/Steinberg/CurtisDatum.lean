module

public import CFSG.LieType.Steinberg.CurtisDatum.RankOne
public import CFSG.LieType.Steinberg.CurtisDatum.Hecke
public import CFSG.LieType.SpecialLinear.CurtisDatum.Cover
public import CFSG.LieType.SpecialLinear.CurtisDatum.NegExcept
public import CFSG.LieType.Steinberg.CentralExt.Unipotent
public import CFSG.Quasithin.Background.SmithCurtisDatum

public section

namespace CFSG.LieType.Steinberg

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.SpecialLinear CFSG.Quasithin.SmithCurtis
open scoped commutatorElement Pointwise

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

set_option hygiene false in
local notation "W" => (coxeterMatrix D.isFiniteType).Group
set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem
set_option hygiene false in
local notation "ρ" => weylAction D.isFiniteType
set_option hygiene false in
local notation "Φ" => RootSystem.ofCartan D.isFiniteType D.divisible

section Elementary

omit [Finite K] in
theorem conj_n_mem_rootGroup_pos (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (i : Fin D.rank) {y : K}
    (hy : y ∈ D.rootGroup (-Pi.single i 1)) :
    n i * y * (n i)⁻¹ ∈ D.rootGroup (Pi.single i 1) := by
  have h := (actsAs_n hct i).conj_mem ((Φ).neg_mem _ ((Φ).single_mem i)) hy
  rwa [map_neg, weylAction_simple_single, neg_neg] at h

omit [Finite K] in
theorem iSup_le_normalizer_negUnipotentExcept
    (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H) (i : Fin D.rank) :
    (⨆ j, H j) ≤ Subgroup.normalizer (negUnipotentExcept D i : Set K) :=
  le_normalizer_iSup₂ fun _ hh γ hγ y hy =>
    Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ
      ((Subgroup.mem_normalizer_iff.mp (iSup_le_normalizer_rootGroup hct hγ.1.1 hh) y).mp hy))

omit [Finite K] in
theorem iSup_H_comm (hext : SteinbergExtras D n H) {a b : K} (ha : a ∈ ⨆ j, H j)
    (hb : b ∈ ⨆ j, H j) : a * b = b * a := by
  refine Subgroup.iSup_induction H (C := fun a => a * b = b * a) ha ?_ ?_ ?_
  · intro i a ha
    refine Subgroup.iSup_induction H (C := fun b => a * b = b * a) hb ?_ ?_ ?_
    · intro j b hb
      exact (hext.torus_commute i j a ha b hb).eq
    · simp
    · intro x y hx hy
      calc a * (x * y) = (a * x) * y := by rw [mul_assoc]
        _ = (x * a) * y := by rw [hx]
        _ = x * (a * y) := by group
        _ = x * (y * a) := by rw [hy]
        _ = x * y * a := by group
  · simp
  · intro x y hx hy
    calc x * y * b = x * (y * b) := by group
      _ = x * (b * y) := by rw [hy]
      _ = (x * b) * y := by group
      _ = (b * x) * y := by rw [hx]
      _ = b * (x * y) := by group

end Elementary

@[expose] noncomputable def curtisDatumOf (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (p : ℕ)
    (hpG : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) :
    CFSG.Quasithin.SmithCurtis.CurtisDatum K
      (coxeterMatrix D.isFiniteType).toCoxeterSystem p where
  U := posUnipotent D
  L := negUnipotent D
  H := ⨆ i, H i
  X i := D.rootGroup (Pi.single i 1)
  Y i := D.rootGroup (-Pi.single i 1)
  Us i := posUnipotentExcept D i
  Q i := negUnipotentExcept D i
  n := n
  nW := nrep hct
  isPGroup_U := isPGroup_iSup_pos hext hpG
  isPGroup_L := by
    have hset : posSet D.roots (-htHom) = {γ | γ ∈ D.roots ∧ ht γ < 0} := by
      ext γ
      simp [posSet, htHom_apply]
    have h := isPGroup_iSup_posSet hext hpG (-htHom)
    rwa [hset] at h
  U_inf_L := posUnipotent_inf_negUnipotent hext
  H_comm := fun a ha b hb => iSup_H_comm hext ha hb
  H_normU := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp
      ((iSup_le_borel.trans (borel_le_normalizer_posUnipotent hct)) hh) u).mp hu
  H_normU' := fun h hh u hu => by
    have hle : (⨆ i, H i) ≤ Subgroup.normalizer (posUnipotent D : Set K) :=
      iSup_le_borel.trans (borel_le_normalizer_posUnipotent hct)
    have h := (Subgroup.mem_normalizer_iff.mp (hle (inv_mem hh)) u).mp hu
    simpa [inv_inv] using h
  H_normL := fun h hh l hl =>
    (Subgroup.mem_normalizer_iff.mp (iSup_le_normalizer_negUnipotent hct hh) l).mp hl
  H_normX := fun s h hh x hx =>
    (Subgroup.mem_normalizer_iff.mp
      (iSup_le_normalizer_rootGroup hct ((Φ).single_mem s) hh) x).mp hx
  H_normQ := fun s h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (iSup_le_normalizer_negUnipotentExcept hct s hh) q).mp hq
  X_le := fun s => rootGroup_le_posUnipotent ((Φ).single_mem s) (ht_single_pos s)
  X_ne_bot := fun s => hext.ne_bot _ ((Φ).single_mem s)
  U_eq := fun s u hu => by
    have hu' : u ∈ (D.rootGroup (Pi.single s 1) : Set K) *
        (posUnipotentExcept D s : Set K) := by
      have hu'' : u ∈ (posUnipotent D : Set K) := hu
      rw [coe_posUnipotent_eq_rootGroup_mul hext s] at hu''
      exact hu''
    obtain ⟨x, hx, v, hv, rfl⟩ := hu'
    exact ⟨x, hx, v, hv, rfl⟩
  Us_le := fun s => posUnipotentExcept_le_posUnipotent s
  X_normUs := fun s x hx v hv =>
    (Subgroup.mem_normalizer_iff.mp (rootGroup_single_le_normalizer hext s hx) v).mp hv
  n_normUs := fun s v hv => conj_n_mem_posUnipotentExcept hct s hv
  n_normUs' := fun s v hv => inv_conj_n_mem_posUnipotentExcept hct s hv
  Y_le := fun s => by
    rw [negUnipotent_eq_sup hext s]
    exact le_sup_right
  Q_le := fun s => negUnipotentExcept_le_negUnipotent s
  L_le := fun s => by
    rw [negUnipotent_eq_sup hext s]
    exact le_of_eq (sup_comm (negUnipotentExcept D s) (D.rootGroup (-Pi.single s 1)))
  X_normQ := fun s x hx q hq =>
    (Subgroup.mem_normalizer_iff.mp (rootGroup_single_le_normalizer_negExcept hext s hx) q).mp hq
  Y_normQ := fun s y hy q hq =>
    (Subgroup.mem_normalizer_iff.mp (rootGroup_neg_single_le_normalizer_negExcept hext s hy) q).mp hq
  n_normQ := fun s q hq => conj_n_mem_negUnipotentExcept hct s hq
  n_conjX := fun s x hx => conj_n_mem_rootGroup_neg hct s hx
  n_conjY := fun s y hy => conj_n_mem_rootGroup_pos hct s hy
  n_sq := fun s => le_iSup H s (by rw [← pow_two]; exact hct.sq_mem s)
  n_normH := fun s h hh => conj_n_mem_iSup hct s hh
  phi i x := rankOnePhi hct hext hBU i x
  psi i x := rankOnePsi hct hext hBU i x
  phi_mem := fun s x hx hx1 => le_iSup H s (rankOnePhi_mem hct hext hBU s hx hx1)
  psi_mem := fun s x hx hx1 => le_iSup H s (rankOnePsi_mem hct hext hBU s hx hx1)
  phi_spec := fun s x hx hx1 => rankOnePhi_spec hct hext hBU s hx hx1
  psi_spec := fun s x hx hx1 => rankOnePsi_spec hct hext hBU s hx hx1
  bruhatY := fun s y hy hy1 => bruhatY_of_rankOne hct hext hBU s hy hy1
  nW_one := nrep_one hct
  nW_simple_mul := fun w s h => nrep_simple_mul hct ((cs).not_isLeftDescent_iff.2 h)
  nW_conj := fun w s h x hx =>
    inversionUnipotent_le_posUnipotent ((cs).simple s * w)
      (rootGroup_inv_single_le_inversionUnipotent (D := D)
        ((cs).not_isLeftDescent_iff.2 h)
        (nrep_inv_conj_mem hct w ((Φ).single_mem s) hx))
  heckeDeg_mul := fun w s h => heckeDeg_n_mul_nrep hct hext hBU w s h
  cover := fun g => exists_cover hct hext g

theorem curtisDatumOf_phi_apply (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (p : ℕ)
    (hpG : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ)) (i : Fin D.rank) (x : K) :
    (curtisDatumOf hct hext hBU p hpG).phi i x = rankOnePhi hct hext hBU i x := by
  unfold curtisDatumOf
  rfl

theorem curtisDatumOf_phi_unique (hct : IsCTGroupDatum cs ρ D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hBU : BruhatExtras D H) (p : ℕ)
    (hpG : ∀ γ ∈ D.roots, IsPGroup p (D.rootGroup γ))
    {i : Fin D.rank} {x : K} (hx : x ∈ D.rootGroup (Pi.single i 1)) (hx1 : x ≠ 1)
    {l h u : K} (hl : l ∈ negUnipotent D) (hh : h ∈ ⨆ j, H j)
    (hu : u ∈ posUnipotent D)
    (he : x * n i = l * h * u) :
    h = (curtisDatumOf hct hext hBU p hpG).phi i x := by
  rw [curtisDatumOf_phi_apply]
  obtain ⟨l', hl', u', hu', he'⟩ := rankOnePhi_spec hct hext hBU i hx hx1
  have hphi_mem := rankOnePhi_mem hct hext hBU i hx hx1
  have heq : (l')⁻¹ * l = rankOnePhi hct hext hBU i x * u' * u⁻¹ * h⁻¹ := by
    have e : l * h * u = l' * rankOnePhi hct hext hBU i x * u' := he.symm.trans he'
    calc (l')⁻¹ * l = (l')⁻¹ * (l * h * u) * (h * u)⁻¹ := by group
      _ = (l')⁻¹ * (l' * rankOnePhi hct hext hBU i x * u') * (h * u)⁻¹ := by rw [e]
      _ = rankOnePhi hct hext hBU i x * u' * u⁻¹ * h⁻¹ := by group
  have hBmem : rankOnePhi hct hext hBU i x * u' * u⁻¹ * h⁻¹ ∈ borel D H :=
    mul_mem (mul_mem (mul_mem (iSup_le_borel (le_iSup H i hphi_mem))
      (posUnipotent_le_borel hu')) (posUnipotent_le_borel (inv_mem hu)))
      (iSup_le_borel (inv_mem hh))
  have hone : (l')⁻¹ * l = 1 := by
    have hmem := Subgroup.mem_inf.2 ⟨heq ▸ hBmem, mul_mem (inv_mem hl') hl⟩
    rw [hBU.borel_inf_negUnipotent, Subgroup.mem_bot] at hmem
    exact hmem
  have hll : l' = l := inv_mul_eq_one.1 hone
  have hcancel : h * u = rankOnePhi hct hext hBU i x * u' := by
    have e : l * h * u = l' * rankOnePhi hct hext hBU i x * u' := he.symm.trans he'
    rw [← hll] at e
    exact mul_left_cancel (by simpa only [mul_assoc] using e)
  have hkey : (rankOnePhi hct hext hBU i x)⁻¹ * h = u' * u⁻¹ := by
    calc (rankOnePhi hct hext hBU i x)⁻¹ * h
        = (rankOnePhi hct hext hBU i x)⁻¹ * (h * u) * u⁻¹ := by group
      _ = (rankOnePhi hct hext hBU i x)⁻¹ *
            (rankOnePhi hct hext hBU i x * u') * u⁻¹ := by rw [hcancel]
      _ = u' * u⁻¹ := by group
  have hmem : (rankOnePhi hct hext hBU i x)⁻¹ * h ∈
      (⨆ j, H j) ⊓ posUnipotent D := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (le_iSup H i hphi_mem)) hh, ?_⟩
    rw [hkey]
    exact mul_mem hu' (inv_mem hu)
  change (rankOnePhi hct hext hBU i x)⁻¹ * h ∈
    (⨆ j, H j) ⊓ (⨆ γ ∈ {γ | γ ∈ D.roots ∧ 0 < ht γ}, D.rootGroup γ) at hmem
  rw [hext.torus_inf_posPart, Subgroup.mem_bot] at hmem
  exact (inv_mul_eq_one.1 hmem).symm

end CFSG.LieType.Steinberg
