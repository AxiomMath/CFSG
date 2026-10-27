module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitStructure
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitDihedral

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Config

abbrev sylowIn (T : Sylow 2 ↥(centralizer ({t} : Set X))) : Subgroup X :=
  (T : Subgroup ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype

omit [Finite X] in
theorem sylowIn_le (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    sylowIn T ≤ centralizer ({t} : Set X) := by
  rintro _ ⟨c, -, rfl⟩
  exact c.2

omit [Finite X] in
theorem isPGroup_sylowIn (T : Sylow 2 ↥(centralizer ({t} : Set X))) : IsPGroup 2 (sylowIn T) :=
  T.isPGroup'.map _

omit [Finite X] in
theorem mem_sylow (h : Config t L) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    t ∈ sylowIn T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set t' : centralizer ({t} : Set X) := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ with ht'
  have hcen : ∀ c : centralizer ({t} : Set X), c * t' = t' * c := fun c =>
    Subtype.ext (mem_centralizer_singleton_iff.mp c.2)
  have hn : (zpowers t').Normal := by
    refine ⟨fun n hn c => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hn
    rw [show c * t' ^ k * c⁻¹ = t' ^ k by rw [((Commute.zpow_right (hcen c) k)).eq]; group]
    exact zpow_mem (mem_zpowers t') k
  have hp : IsPGroup 2 (zpowers t') := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht', Subgroup.orderOf_mk, h.orderOf_eq, pow_one])
  exact ⟨t', hp.le_sylow_of_normal T (mem_zpowers t'), rfl⟩

theorem factorization_card_L (h : Config t L) : (Nat.card L).factorization 2 = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 L)
  have hodd : ¬ 2 ∣ Nat.card (pPrimeCore 2 L) := fun h2 =>
    (Nat.not_even_iff_odd.mpr odd_card_pPrimeCore) (even_iff_two_dvd.mpr h2)
  obtain ⟨P, hP⟩ := h.exists_sylow
  have hQ : (Nat.card (L ⧸ pPrimeCore 2 L)).factorization 2 = 3 := by
    have := Sylow.card_eq_multiplicity P
    rw [hP] at this
    have h8 : (2 : ℕ) ^ 3 = 2 ^ (Nat.card (L ⧸ pPrimeCore 2 L)).factorization 2 := by
      rw [← this]; norm_num
    exact (Nat.pow_right_injective le_rfl h8).symm
  rw [hcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
    hQ, Nat.factorization_eq_zero_of_not_dvd hodd]

theorem card_inf_L (h : Config t L) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    Nat.card (sylowIn T ⊓ L : Subgroup X) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLC := h.le_centralizer
  have hLN := h.le_normalizer
  have hup : Nat.card (sylowIn T ⊓ L : Subgroup X) ≤ 8 := by
    have h2 : IsPGroup 2 ((sylowIn T ⊓ L : Subgroup X).subgroupOf L) :=
      (isPGroup_sylowIn T).to_inf_left.comap_of_injective L.subtype (subtype_injective L)
    obtain ⟨Q, hQ⟩ := h2.exists_le_sylow
    have hcQ : Nat.card Q = 8 := by
      rw [Sylow.card_eq_multiplicity, h.factorization_card_L]; norm_num
    have := Subgroup.card_le_of_le hQ
    rw [hcQ, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : sylowIn T ⊓ L ≤ L)).toEquiv]
      at this
    exact this
  obtain ⟨Q⟩ : Nonempty (Sylow 2 L) := inferInstance
  have hcQ : Nat.card Q = 8 := by
    rw [Sylow.card_eq_multiplicity, h.factorization_card_L]; norm_num
  set Q' : Subgroup (centralizer ({t} : Set X)) :=
    ((Q : Subgroup L).map L.subtype).comap (centralizer ({t} : Set X)).subtype with hQ'
  have hQ'p : IsPGroup 2 Q' := (Q.isPGroup'.map L.subtype).comap_of_injective _
    (subtype_injective _)
  obtain ⟨T', hT'⟩ := hQ'p.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set X)) T' T
  have hsub : ((Q : Subgroup L).map L.subtype).map (MulAut.conj (g : X)).toMonoidHom ≤
      sylowIn T ⊓ L := by
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have hqC : (q : X) ∈ centralizer ({t} : Set X) := hLC q.2
      have hqT' : (⟨q, hqC⟩ : centralizer ({t} : Set X)) ∈
          (T' : Subgroup (centralizer ({t} : Set X))) := hT' (by
        rw [mem_comap]; exact ⟨q, hq, rfl⟩)
      have : g * (⟨q, hqC⟩ : centralizer ({t} : Set X)) * g⁻¹ ∈
          (T : Subgroup (centralizer ({t} : Set X))) := by
        rw [← hg, Sylow.coe_subgroup_smul]
        exact ⟨_, hqT', rfl⟩
      exact ⟨_, this, rfl⟩
    · have := (mem_normalizer_iff.mp (hLN g.2) q).mp q.2
      simpa [MulAut.conj_apply] using this
  have hlow : 8 ≤ Nat.card (sylowIn T ⊓ L : Subgroup X) := by
    have := Subgroup.card_le_of_le hsub
    rw [card_map_of_injective (MulAut.conj (g : X)).injective,
      card_map_of_injective L.subtype_injective, hcQ] at this
    exact this
  omega

theorem injective_mk_of_isPGroup {P : Subgroup L} (hP : IsPGroup 2 P) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore 2 L)).comp P.subtype) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro p hp
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hp
  have hdisj : P ⊓ pPrimeCore 2 L = ⊥ := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    exact (Subgroup.disjoint_of_coprime_natCard (by
      rw [hk]
      exact Nat.Coprime.pow_left k (pPrimeCore_coprime_card (p := 2) (G := L)))).eq_bot
  have : (p : L) ∈ P ⊓ pPrimeCore 2 L := ⟨p.2, hp⟩
  rw [hdisj, mem_bot] at this
  rw [mem_bot]
  exact Subtype.ext this

theorem inf_L_mulEquiv_dihedral (h : Config t L) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    Nonempty ((sylowIn T ⊓ L : Subgroup X) ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs := h.isSimpleGroup
  set R := (sylowIn T ⊓ L : Subgroup X) with hR
  set R' : Subgroup L := R.subgroupOf L with hR'
  have hRR' : R ≃* R' := (subgroupOfEquivOfLe (inf_le_right : R ≤ L)).symm
  have hR'p : IsPGroup 2 R' :=
    ((isPGroup_sylowIn T).to_inf_left).comap_of_injective L.subtype (subtype_injective L)
  set f := (QuotientGroup.mk' (pPrimeCore 2 L)).comp R'.subtype with hf
  have hinj : Function.Injective f := injective_mk_of_isPGroup hR'p
  let e : R' ≃* f.range := MonoidHom.ofInjective hinj
  have hcard : Nat.card f.range = 8 := by
    rw [← Nat.card_congr e.toEquiv, ← Nat.card_congr hRR'.toEquiv, hR, h.card_inf_L T]
  let S : Sylow 2 (L ⧸ pPrimeCore 2 L) := Sylow.ofCard f.range (by
    rw [hcard]
    obtain ⟨P, hP⟩ := h.exists_sylow
    rw [← hP, Sylow.card_eq_multiplicity])
  obtain ⟨eD⟩ := sylow_mulEquiv_dihedral_of_simple h.quot_nonabelian h.pRank_eq S
    (h.card_sylow S)
  have hS : (S : Subgroup (L ⧸ pPrimeCore 2 L)) = f.range := Sylow.coe_ofCard _ _
  exact ⟨hRR'.trans (e.trans ((MulEquiv.subgroupCongr hS.symm).trans eD))⟩

theorem eq_one_of_mem_oddCoreIn_of_isPGroup {P : Subgroup X} (hP : IsPGroup 2 P) {g : X}
    (hgP : g ∈ P) (hg : g ∈ (pPrimeCore 2 L).map L.subtype) : g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdisj : P ⊓ (pPrimeCore 2 L).map L.subtype = ⊥ := by
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    exact (Subgroup.disjoint_of_coprime_natCard (by
      rw [hk, card_map_of_injective L.subtype_injective]
      exact Nat.Coprime.pow_left k (pPrimeCore_coprime_card (p := 2) (G := L)))).eq_bot
  have : g ∈ P ⊓ (pPrimeCore 2 L).map L.subtype := ⟨hgP, hg⟩
  rwa [hdisj, mem_bot] at this

theorem inf_kernel_le_oddCore (h : Config t L) :
    L ⊓ coreActionKernel L ≤ (pPrimeCore 2 L).map L.subtype := by
  rintro g ⟨hgL, -, hg⟩
  set g' : L := ⟨g, hgL⟩ with hg'
  refine ⟨g', ?_, rfl⟩
  have hc : (QuotientGroup.mk g' : L ⧸ pPrimeCore 2 L) ∈ center (L ⧸ pPrimeCore 2 L) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨o, ho, hoe⟩ := hg j j.2
    have heq : j⁻¹ * g'⁻¹ * j * g' = o := by
      apply Subtype.ext
      simpa [hg'] using hoe.symm
    have h2 : (QuotientGroup.mk (j⁻¹ * g'⁻¹ * j * g') : L ⧸ pPrimeCore 2 L) = 1 := by
      rw [heq]
      exact (QuotientGroup.eq_one_iff o).mpr ho
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h2
    have h3 := congrArg (fun x => (QuotientGroup.mk g' : L ⧸ pPrimeCore 2 L) *
      (QuotientGroup.mk j : L ⧸ pPrimeCore 2 L) * x) h2
    simp only [mul_one] at h3
    rw [show (QuotientGroup.mk g' : L ⧸ pPrimeCore 2 L) * (QuotientGroup.mk j) *
        ((QuotientGroup.mk j)⁻¹ * (QuotientGroup.mk g')⁻¹ * (QuotientGroup.mk j) *
          (QuotientGroup.mk g')) = (QuotientGroup.mk j) * (QuotientGroup.mk g') by group] at h3
    exact h3
  rw [h.center_quot_eq_bot, mem_bot, QuotientGroup.eq_one_iff] at hc
  exact hc

omit [Finite X] in
theorem isCyclic_inf_kernel (h : Config t L) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    IsCyclic (sylowIn T ⊓ coreActionKernel L : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := (sylowIn T ⊓ coreActionKernel L : Subgroup X) with hK
  have hKC : K ≤ coreActionKernel L := inf_le_right
  have hK2 : IsPGroup 2 (K.subgroupOf (coreActionKernel L)) :=
    ((isPGroup_sylowIn T).to_inf_left).comap_of_injective _ (subtype_injective _)
  obtain ⟨P, hP⟩ := hK2.exists_le_sylow
  have hPc := h.isCyclic P
  have : IsCyclic (K.subgroupOf (coreActionKernel L)) := Subgroup.isCyclic_of_le hP
  exact (subgroupOfEquivOfLe hKC).isCyclic.mp this

omit [Finite X] in
theorem mem_inf_kernel (h : Config t L) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    t ∈ (sylowIn T ⊓ coreActionKernel L : Subgroup X) :=
  ⟨h.mem_sylow T, GSLit.mem_coreActionKernel_of_le_centralizer h.le_centralizer⟩

theorem inf_kernel_inf_L (h : Config t L) (T : Sylow 2 ↥(centralizer ({t} : Set X))) :
    (sylowIn T ⊓ coreActionKernel L ⊓ L : Subgroup X) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨⟨hgT, hgK⟩, hgL⟩
  rw [mem_bot]
  exact eq_one_of_mem_oddCoreIn_of_isPGroup (isPGroup_sylowIn T) hgT
    (h.inf_kernel_le_oddCore ⟨hgL, hgK⟩)

theorem commute_inf_L_inf_kernel (T : Sylow 2 ↥(centralizer ({t} : Set X))) {r k : X}
    (hr : r ∈ (sylowIn T ⊓ L : Subgroup X))
    (hk : k ∈ (sylowIn T ⊓ coreActionKernel L : Subgroup X)) : r * k = k * r := by
  have h1 : r⁻¹ * k⁻¹ * r * k ∈ (pPrimeCore 2 L).map L.subtype := hk.2.2 r hr.2
  have h2 : r⁻¹ * k⁻¹ * r * k ∈ sylowIn T :=
    mul_mem (mul_mem (mul_mem (inv_mem hr.1) (inv_mem hk.1)) hr.1) hk.1
  have h3 := eq_one_of_mem_oddCoreIn_of_isPGroup (isPGroup_sylowIn T) h2 h1
  have : k⁻¹ * r * k = r := by
    calc k⁻¹ * r * k = r * (r⁻¹ * k⁻¹ * r * k) := by group
      _ = r := by rw [h3, mul_one]
  calc r * k = k * (k⁻¹ * r * k) := by group
    _ = k * r := by rw [this]

end Config

end CFSG.ComponentClassification.HSFLit
