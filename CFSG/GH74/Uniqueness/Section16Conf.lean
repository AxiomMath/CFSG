module

public import CFSG.GH74.Uniqueness.Section16Stmts
public import CFSG.GH74.Uniqueness.Section4Basic

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem conjugate_conj_eq_of_mem {t d : X} (hd : d ∈ M ⊓ conjugate M t) :
    conjugate M (d⁻¹ * t * d) = conjugate M t := by
  have hdM : d⁻¹ ∈ normalizer (M : Set X) :=
    Subgroup.le_normalizer (M.inv_mem (Subgroup.mem_inf.mp hd).1)
  have hdt : d ∈ normalizer (conjugate M t : Set X) :=
    Subgroup.le_normalizer (Subgroup.mem_inf.mp hd).2
  rw [← conjugate_conjugate, ← conjugate_conjugate, conjugate_eq_iff_mem_normalizer.mpr hdM,
    conjugate_eq_iff_mem_normalizer.mpr hdt]

theorem exists_conj_commute_of_odd {D : Subgroup X} {t u : X}
    (hodd : Odd (Nat.card {y : X // ∃ d ∈ D, y = d⁻¹ * t * d})) (hu : u ∈ D) (hu2 : u * u = 1) :
    ∃ d ∈ D, (d⁻¹ * t * d) * u = u * (d⁻¹ * t * d) := by
  classical
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hmem : ∀ y : {y : X // ∃ d ∈ D, y = d⁻¹ * t * d},
      ∃ d ∈ D, u * (y : X) * u = d⁻¹ * t * d := by
    rintro ⟨y, d, hd, rfl⟩
    refine ⟨d * u, D.mul_mem hd hu, ?_⟩
    calc u * (d⁻¹ * t * d) * u = (d * u⁻¹)⁻¹ * t * (d * u) := by group
      _ = (d * u)⁻¹ * t * (d * u) := by rw [hui]
  let f : {y : X // ∃ d ∈ D, y = d⁻¹ * t * d} → {y : X // ∃ d ∈ D, y = d⁻¹ * t * d} :=
    fun y => ⟨u * y * u, hmem y⟩
  have hf : Function.Involutive f := by
    intro y
    apply Subtype.ext
    change u * (u * (y : X) * u) * u = y
    calc u * (u * (y : X) * u) * u = (u * u) * y * (u * u) := by group
      _ = y := by rw [hu2, one_mul, mul_one]
  have : Fintype {y : X // ∃ d ∈ D, y = d⁻¹ * t * d} := Fintype.ofFinite _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hndvd : ¬ 2 ∣ Fintype.card {y : X // ∃ d ∈ D, y = d⁻¹ * t * d} := by
    rw [Fintype.card_eq_nat_card]
    exact fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hσ : (hf.toPerm f) ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    exact Equiv.ext fun y => hf y
  obtain ⟨⟨y, d, hd, rfl⟩, hy⟩ := Equiv.Perm.exists_fixed_point_of_prime hndvd hσ
  refine ⟨d, hd, ?_⟩
  have hy' : u * (d⁻¹ * t * d) * u = d⁻¹ * t * d := congrArg Subtype.val hy
  calc (d⁻¹ * t * d) * u = (u * (d⁻¹ * t * d) * u) * u := by rw [hy']
    _ = u * (d⁻¹ * t * d) * (u * u) := by group
    _ = u * (d⁻¹ * t * d) := by rw [hu2, mul_one]

theorem ZDSetup.exists_conj_commute (S : ZDSetup X Z M) {t : X} (ht : t ∈ Z) (htM : t ∉ M)
    {u : X} (hu : u ∈ M ⊓ conjugate M t) (hu2 : u * u = 1) :
    ∃ d ∈ M ⊓ conjugate M t, (d⁻¹ * t * d) * u = u * (d⁻¹ * t * d) := by
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  refine exists_conj_commute_of_odd ?_ hu hu2
  rw [card_conj_orbit, (S.prodDisc.prop36d S.invariant ht htM hz hzM).2.2.1]
  exact S.odd_zNum

theorem ZDSetup.exists_sylow_central_ge (S : ZDSetup X Z M) {R : Subgroup X} (hRM : R ≤ M)
    (hR : IsPGroup 2 R) :
    ∃ V : Subgroup X, IsPGroup 2 V ∧ R ≤ V ∧
      ∃ z₁ ∈ Z, z₁ ∈ M ∧ z₁ ∈ V ∧ ∀ s ∈ V, s * z₁ = z₁ * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  obtain ⟨T, hTM, hzT, hcomm⟩ := S.exists_sylow_central hz hzM
  have hR' : IsPGroup 2 (R.subgroupOf M) := hR.comap_subtype
  obtain ⟨Q, hQ⟩ := hR'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq M Q (T.subtype hTM)
  have hRT : ∀ r ∈ R, (h : X) * r * (h : X)⁻¹ ∈ (T : Subgroup X) := by
    intro r hr
    have hrQ : r ∈ (Q : Subgroup ↥M).map M.subtype :=
      ⟨⟨r, hRM hr⟩, hQ (Subgroup.mem_subgroupOf.mpr hr), rfl⟩
    have hmem := mem_map_smul Q h hrQ
    rwa [hh, map_subtype_sylow_subtype T hTM] at hmem
  have hz₁ : (h : X) * ((h : X)⁻¹ * z * h) * (h : X)⁻¹ = z := by group
  refine ⟨conjugate (T : Subgroup X) h, T.isPGroup'.map _,
    fun r hr => mem_conjugate_iff.mpr (hRT r hr), (h : X)⁻¹ * z * h, S.invariant.2 z hz h,
    M.mul_mem (M.mul_mem (M.inv_mem h.2) hzM) h.2, ?_, fun s hs => ?_⟩
  · rw [mem_conjugate_iff, hz₁]
    exact hzT
  · have hs' := hcomm _ (mem_conjugate_iff.mp hs)
    calc s * ((h : X)⁻¹ * z * h) = (h : X)⁻¹ * (((h : X) * s * (h : X)⁻¹) * z) * h := by group
      _ = (h : X)⁻¹ * (z * ((h : X) * s * (h : X)⁻¹)) * h := by rw [hs']
      _ = ((h : X)⁻¹ * z * h) * s := by group

omit [Finite X] in
theorem exists_isSylowOf_ge_of_le {p : ℕ} [Fact p.Prime] {Q K : Subgroup X} (hQK : Q ≤ K)
    (hQ : IsPGroup p Q) : ∃ P : Subgroup X, ABGLocalTools.IsSylowOf p P K ∧ Q ≤ P := by
  have hQ' : IsPGroup p (Q.subgroupOf K) := hQ.comap_subtype
  obtain ⟨T, hT⟩ := hQ'.exists_le_sylow
  refine ⟨(T : Subgroup K).map K.subtype, ⟨T, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hQK hx⟩, hT (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem mem_of_isSylowOf_centralizer {u : X} (huM : u ∈ M) (hu2 : orderOf u = 2) {T : Subgroup X}
    (hT : ABGLocalTools.IsSylowOf 2 T (centralizer ({u} : Set X) ⊓ M)) : u ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hT
  have huBM : u ∈ centralizer ({u} : Set X) ⊓ M :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, huM⟩
  have hcent : (⟨u, huBM⟩ : ↥(centralizer ({u} : Set X) ⊓ M)) ∈
      center ↥(centralizer ({u} : Set X) ⊓ M) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).1)
  have hz2 : IsPGroup 2 (zpowers (⟨u, huBM⟩ : ↥(centralizer ({u} : Set X) ⊓ M))) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu2, pow_one]
  exact ⟨_, mem_sylow_of_mem_center Q hcent hz2, rfl⟩

theorem ZDSetup.exists_conf16 (S : ZDSetup X Z M) (c : Ctx16 Z M) : Nonempty (Conf16 Z M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIne : {v : X | v ∈ M ⊓ conjugate M c.t ∧ orderOf v = 2}.Nonempty := by
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥(M ⊓ conjugate M c.t)) 2
      (even_iff_two_dvd.mp c.hD)
    exact ⟨v, v.2, by rw [Subgroup.orderOf_coe]; exact hv⟩
  obtain ⟨u, ⟨huD, hu2⟩, hmax⟩ := Set.exists_max_image _
    (fun v => (Z ∩ ((centralizer ({v} : Set X) ⊓ M : Subgroup X) : Set X)).ncard)
    (Set.toFinite _) hIne
  have hu2' : u * u = 1 := by rw [← sq, ← hu2, pow_orderOf_eq_one]
  have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
  obtain ⟨d, hdD, hdcomm⟩ := S.exists_conj_commute c.ht c.htM huD hu2'
  have hDt : conjugate M (d⁻¹ * c.t * d) = conjugate M c.t := conjugate_conj_eq_of_mem hdD
  have ht₁M : d⁻¹ * c.t * d ∉ M := by
    intro h
    have hdM := (Subgroup.mem_inf.mp hdD).1
    have e : d * (d⁻¹ * c.t * d) * d⁻¹ = c.t := by group
    exact c.htM (e ▸ M.mul_mem (M.mul_mem hdM h) (M.inv_mem hdM))
  obtain ⟨P, hP⟩ := ABGLocalTools.exists_isSylowOf 2 (zHull Z (centralizer ({u} : Set X)) ⊓ M)
  have hPle : P ≤ centralizer ({u} : Set X) ⊓ M :=
    hP.le.trans (inf_le_inf_right M ((Subgroup.closure_le _).mpr Set.inter_subset_right))
  obtain ⟨T₁, hT₁, hPT₁⟩ := exists_isSylowOf_ge_of_le hPle hP.isPGroup
  obtain ⟨V, hV, hT₁V, z₁, hz₁Z, hz₁M, hz₁V, hz₁c⟩ :=
    S.exists_sylow_central_ge (hT₁.le.trans inf_le_right) hT₁.isPGroup
  have huT₁ : u ∈ T₁ := mem_of_isSylowOf_centralizer huM hu2 hT₁
  have hz₁B : z₁ ∈ centralizer ({u} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hz₁c u (hT₁V huT₁)).symm
  have hVT₁ : V ⊓ (centralizer ({u} : Set X) ⊓ M) = T₁ :=
    hT₁.eq_of_le (le_inf hT₁V hT₁.le) inf_le_right hV.to_inf_left
  have hz₁T₁ : z₁ ∈ T₁ := by
    rw [← hVT₁]
    exact Subgroup.mem_inf.mpr ⟨hz₁V, Subgroup.mem_inf.mpr ⟨hz₁B, hz₁M⟩⟩
  exact ⟨{ t := d⁻¹ * c.t * d
           z := z₁
           ht := S.invariant.2 _ c.ht d
           htM := ht₁M
           hz := hz₁Z
           hzM := hz₁M
           hD := hDt ▸ c.hD
           u := u
           hu := hDt ▸ huD
           hu2 := hu2
           hmax := fun v hv hv2 => hmax v ⟨hDt ▸ hv, hv2⟩
           P := P
           T1 := T₁
           hP := hP
           hT1 := hT₁
           hPT1 := hPT₁
           ht_B := Subgroup.mem_centralizer_singleton_iff.mpr hdcomm
           hz_T1 := ⟨hz₁T₁, fun y hy => hz₁c y (hT₁V hy)⟩ }⟩

end CFSG.GH74.Uniqueness
