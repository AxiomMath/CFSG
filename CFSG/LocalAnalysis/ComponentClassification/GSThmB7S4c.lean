module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4b
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L2b

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Seven

variable {X : Type} [Group X] [Finite X]

noncomputable abbrev rhoImg (J W : Subgroup X) : Subgroup (MulAut (↥J ⧸ pPrimeCore 2 ↥J)) :=
  (W.subgroupOf (normalizer (J : Set X))).map (Eight.oddBarAction J)

omit [Finite X] in
theorem rho_injOn {J W : Subgroup X} (hW : W ⊓ coreActionKernel J = ⊥) :
    Set.InjOn (Eight.oddBarAction J) (W.subgroupOf (normalizer (J : Set X)) : Set _) := by
  intro u hu v hv huv
  have h1 : u * v⁻¹ ∈ (Eight.oddBarAction J).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, huv, mul_inv_cancel]
  have h2 : ((u * v⁻¹ : ↥(normalizer (J : Set X))) : X) ∈ W ⊓ coreActionKernel J :=
    mem_inf.mpr ⟨mul_mem (mem_subgroupOf.mp hu) (inv_mem (mem_subgroupOf.mp hv)),
      Eight.mem_ker_oddBarAction.mp h1⟩
  rw [hW, mem_bot] at h2
  have h3 : u * v⁻¹ = 1 := Subtype.ext h2
  exact mul_inv_eq_one.mp h3

noncomputable def rhoEquiv {J W A : Subgroup X} (hWN : W ≤ normalizer (J : Set X))
    (hW : W ⊓ coreActionKernel J = ⊥) (hAW : A ≤ W) : ↥A ≃* ↥(rhoImg J A) :=
  (subgroupOfEquivOfLe (hAW.trans hWN)).symm.trans
    (MulEquiv.ofBijective ((Eight.oddBarAction J).subgroupMap (A.subgroupOf (normalizer J)))
      ⟨fun u v huv => Subtype.ext (rho_injOn hW
        (show (u : ↥(normalizer (J : Set X))) ∈ W.subgroupOf (normalizer (J : Set X)) from
          hAW (mem_subgroupOf.mp u.2))
        (show (v : ↥(normalizer (J : Set X))) ∈ W.subgroupOf (normalizer (J : Set X)) from
          hAW (mem_subgroupOf.mp v.2)) (congrArg Subtype.val huv)),
        (Eight.oddBarAction J).subgroupMap_surjective _⟩)

omit [Finite X] in
theorem card_rhoImg {J W A : Subgroup X} (hWN : W ≤ normalizer (J : Set X))
    (hW : W ⊓ coreActionKernel J = ⊥) (hAW : A ≤ W) : Nat.card (rhoImg J A) = Nat.card A :=
  (Nat.card_congr (rhoEquiv hWN hW hAW).toEquiv).symm

omit [Finite X] in
theorem rho_of_mem {J : Subgroup X} {d : X} (hd : d ∈ J) :
    Eight.oddBarAction J ⟨d, le_normalizer hd⟩ =
      MulAut.conj (((⟨d, hd⟩ : ↥J)) : ↥J ⧸ pPrimeCore 2 ↥J) :=
  Eight.oddBarAction_of_mem ⟨d, hd⟩

omit [Finite X] in
theorem rhoImg_eq_innOf {J D : Subgroup X} (hDJ : D ≤ J) :
    rhoImg J D = innOf ((D.subgroupOf J).map (QuotientGroup.mk' (pPrimeCore 2 ↥J))) := by
  ext σ
  constructor
  · rintro ⟨⟨d, hdN⟩, hd, rfl⟩
    have hdJ : d ∈ J := hDJ (mem_subgroupOf.mp hd)
    refine ⟨QuotientGroup.mk' (pPrimeCore 2 ↥J) ⟨d, hdJ⟩, ⟨⟨d, hdJ⟩, mem_subgroupOf.mpr
      (mem_subgroupOf.mp hd), rfl⟩, ?_⟩
    exact (rho_of_mem hdJ).symm
  · rintro ⟨_, ⟨⟨d, hdJ⟩, hd, rfl⟩, rfl⟩
    refine ⟨⟨d, le_normalizer hdJ⟩, mem_subgroupOf.mpr (mem_subgroupOf.mp hd), ?_⟩
    exact rho_of_mem hdJ

omit [Finite X] in
theorem le_centralizer_self_of_card_two {G : Type*} [Group G] {H : Subgroup G}
    (h : Nat.card H = 2) : H ≤ centralizer (H : Set G) := by
  have : Fact (Nat.card H).Prime := ⟨h ▸ Nat.prime_two⟩
  have hc : IsCyclic H := isCyclic_of_prime_card rfl
  intro x hx
  rw [mem_centralizer_iff]
  intro y hy
  have := (IsCyclic.commGroup (α := H)).mul_comm ⟨y, hy⟩ ⟨x, hx⟩
  exact congrArg Subtype.val this

omit [Finite X] in
theorem card_conjugate (A : Subgroup X) (g : X) : Nat.card (conjugate A g) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

noncomputable def conjugateEquiv (A : Subgroup X) (g : X) : ↥A ≃* ↥(conjugate A g) :=
  A.equivMapOfInjective _ (MulAut.conj g⁻¹).injective

namespace Setting

variable (s : Setting X)

theorem conjugate_P_inf_kernel {g : X} (hg : g ∈ normalizer (s.h.S : Set X))
    (hga : g⁻¹ * s.h.a * g ≠ s.h.a) : conjugate s.h.P g ⊓ coreActionKernel s.h.J = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwg, hwK⟩ := mem_inf.mp hw
  have hwP : w ∈ s.h.P := mem_inf.mpr ⟨s.conjugate_P_le_S hg hwg, hwK⟩
  have := s.P_inf_conjugate_eq_bot hg hga ▸ mem_inf.mpr ⟨hwP, hwg⟩
  exact this

theorem conjugate_P_le_normalizer {g : X} (hg : g ∈ normalizer (s.h.S : Set X)) :
    conjugate s.h.P g ≤ normalizer (s.h.J : Set X) :=
  (s.conjugate_P_le_S hg).trans s.h.S_le_normalizer

theorem cfl2A_apply (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer)
    (hCent : CFL2Cent) (hD : CFSp4D) (hA : CFL2A) {g : X}
    (hg : g ∈ normalizer (s.h.S : Set X)) (hga : g⁻¹ * s.h.a * g ≠ s.h.a) :
    Nat.card (B0 s.h s.y) = 2 ∧ (∀ T : Sylow 2 (s.h.J ⧸ pPrimeCore 2 s.h.J), 8 ≤ Nat.card T) ∧
      ∃ T : Sylow 2 (s.h.J ⧸ pPrimeCore 2 s.h.J),
        innOf (T : Subgroup (s.h.J ⧸ pPrimeCore 2 s.h.J)) ≤ rhoImg s.h.J (conjugate s.h.P g) ∧
        rhoImg s.h.J (conjugate (B0 s.h s.y) g) ≤
          centralizer (innOf (T : Subgroup (s.h.J ⧸ pPrimeCore 2 s.h.J)) :
            Set (MulAut (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D₁, hD₁P, hD₁L, T, ⟨eT⟩⟩ := s.exists_D1 hConj hComp hOut hCent hD
  set W := conjugate s.h.P g with hWdef
  have hWN := s.conjugate_P_le_normalizer hg
  have hW := s.conjugate_P_inf_kernel hg hga
  have hB0P : B0 s.h s.y ≤ s.h.P := s.B0_le_B.trans s.h.B_le_P
  have hD₁W : conjugate D₁ g ≤ W := map_mono hD₁P
  have hB₀W : conjugate (B0 s.h s.y) g ≤ W := map_mono hB0P
  have hR2 : IsPGroup 2 (rhoImg s.h.J W) := by
    have hW2 : IsPGroup 2 W := s.h.isPGroup_S.to_le (s.conjugate_P_le_S hg)
    exact (hW2.of_equiv (subgroupOfEquivOfLe hWN).symm).map _
  have hcomm : rhoImg s.h.J (conjugate (B0 s.h s.y) g) ≤ centralizer
      (rhoImg s.h.J (conjugate D₁ g) : Set (MulAut (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J))) := by
    rintro _ ⟨⟨e, heN⟩, he, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨d, hdN⟩, hd, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    change d * e = e * d
    have he' := mem_subgroupOf.mp he
    have hd' := mem_subgroupOf.mp hd
    rw [mem_conjugate_iff] at he' hd'
    have hc : (g * d * g⁻¹) * (g * e * g⁻¹) = (g * e * g⁻¹) * (g * d * g⁻¹) :=
      (mem_centralizer_iff.mp (s.L_le_centralizer (hD₁L hd')) _ he').symm
    calc d * e = g⁻¹ * ((g * d * g⁻¹) * (g * e * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * e * g⁻¹) * (g * d * g⁻¹)) * g := by rw [hc]
      _ = e * d := by group
  have hdisj : rhoImg s.h.J (conjugate D₁ g) ⊓ rhoImg s.h.J (conjugate (B0 s.h s.y) g) = ⊥ := by
    rw [eq_bot_iff]
    rintro σ ⟨⟨⟨d, hdN⟩, hd, rfl⟩, ⟨⟨e, heN⟩, he, he'⟩⟩
    have hde : (⟨e, heN⟩ : ↥(normalizer (s.h.J : Set X))) = ⟨d, hdN⟩ :=
      rho_injOn hW (show _ ∈ W.subgroupOf _ from hB₀W (mem_subgroupOf.mp he))
        (show _ ∈ W.subgroupOf _ from hD₁W (mem_subgroupOf.mp hd)) he'
    have hed : e = d := congrArg Subtype.val hde
    have hd1 : d ∈ conjugate D₁ g := mem_subgroupOf.mp hd
    have he1 : e ∈ conjugate (B0 s.h s.y) g := mem_subgroupOf.mp he
    rw [hed, mem_conjugate_iff] at he1
    rw [mem_conjugate_iff] at hd1
    have h0 : g * d * g⁻¹ = 1 := by
      have := s.B0_inf_L ▸ mem_inf.mpr ⟨he1, hD₁L hd1⟩
      exact mem_bot.mp this
    have hd0 : d = 1 := by
      calc d = g⁻¹ * (g * d * g⁻¹) * g := by group
        _ = 1 := by rw [h0]; group
    rw [mem_bot]
    change Eight.oddBarAction s.h.J ⟨d, hdN⟩ = 1
    rw [show (⟨d, hdN⟩ : ↥(normalizer (s.h.J : Set X))) = 1 from Subtype.ext hd0, map_one]
  have hne : rhoImg s.h.J (conjugate (B0 s.h s.y) g) ≠ ⊥ := by
    intro hbot
    apply s.hB0
    rw [eq_bot_iff]
    intro b hb
    have hbg : g⁻¹ * b * g ∈ conjugate (B0 s.h s.y) g := by
      rw [mem_conjugate_iff, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
      exact hb
    have h1 : Eight.oddBarAction s.h.J ⟨g⁻¹ * b * g, hWN (hB₀W hbg)⟩ ∈
        rhoImg s.h.J (conjugate (B0 s.h s.y) g) := mem_map_of_mem _ (mem_subgroupOf.mpr hbg)
    rw [hbot, mem_bot] at h1
    have h2 := rho_injOn hW (show _ ∈ W.subgroupOf _ from hB₀W hbg)
      (show (1 : ↥(normalizer (s.h.J : Set X))) ∈ W.subgroupOf _ from one_mem _)
      (by rw [h1, map_one])
    have h3 : g⁻¹ * b * g = 1 := congrArg Subtype.val h2
    rw [mem_bot]
    calc b = g * (g⁻¹ * b * g) * g⁻¹ := by group
      _ = 1 := by rw [h3]; group
  obtain ⟨hE2, h8, T, hT⟩ := hA _ s.p s.f s.hp s.hp2 s.hf s.hJLie (rhoImg s.h.J W)
    (rhoImg s.h.J (conjugate D₁ g)) (rhoImg s.h.J (conjugate (B0 s.h s.y) g)) hR2
    (map_mono (fun w hw => hD₁W hw)) (map_mono (fun w hw => hB₀W hw)) hcomm hdisj hne
    ⟨T, ⟨(rhoEquiv hWN hW hD₁W).symm.trans ((conjugateEquiv D₁ g).symm.trans eT)⟩⟩
  have hE2' : Nat.card (rhoImg s.h.J (conjugate (B0 s.h s.y) g)) = 2 := hE2
  refine ⟨?_, h8, T, hT.trans (sup_le (map_mono (fun w hw => hD₁W hw))
    (map_mono (fun w hw => hB₀W hw))), ?_⟩
  · rw [← card_conjugate (B0 s.h s.y) g, ← card_rhoImg hWN hW hB₀W]
    exact hE2
  · rw [le_centralizer_iff]
    exact hT.trans (sup_le (le_centralizer_iff.mp hcomm) (le_centralizer_self_of_card_two hE2'))

end Setting

omit [Finite X] in
theorem conjugate_centralizer_singleton (a g : X) :
    conjugate (centralizer ({a} : Set X)) g = centralizer ({g⁻¹ * a * g} : Set X) := by
  ext w
  rw [mem_conjugate_iff, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc w * (g⁻¹ * a * g) = g⁻¹ * ((g * w * g⁻¹) * a) * g := by group
      _ = g⁻¹ * (a * (g * w * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * a * g * w := by group
  · intro h
    calc g * w * g⁻¹ * a = g * (w * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * a * g) * w) * g⁻¹ := by rw [h]
      _ = a * (g * w * g⁻¹) := by group

theorem isSylowIn_of_card {S C S' C' : Subgroup X} (hSC : S ≤ C) (hS2 : IsPGroup 2 S)
    (hS' : IsSylowIn S' C') (hcard : Nat.card S = Nat.card S') (hCC : Nat.card C = Nat.card C') :
    IsSylowIn S C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS'C', R, hR⟩ := hS'
  have hidx' : ¬ 2 ∣ (S'.subgroupOf C').index := by
    rw [← hR]
    exact R.not_dvd_index
  have h1 := Subgroup.index_mul_card (S.subgroupOf C)
  have h2 := Subgroup.index_mul_card (S'.subgroupOf C')
  rw [Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv] at h1
  rw [Nat.card_congr (subgroupOfEquivOfLe hS'C').toEquiv] at h2
  have hpos : 0 < Nat.card S := Nat.card_pos
  have hidx : (S.subgroupOf C).index = (S'.subgroupOf C').index := by
    rw [← hcard] at h2
    rw [hCC] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  have hP : IsPGroup 2 (S.subgroupOf C) := hS2.comap_subtype
  refine ⟨hSC, hP.toSylow (hidx ▸ hidx'), ?_⟩
  exact IsPGroup.toSylow_coe hP _

theorem exists_normalizer_conj_of_sylow {S : Subgroup X} {a t g : X}
    (hSa : IsSylowIn S (centralizer ({a} : Set X))) (hSt : S ≤ centralizer ({t} : Set X))
    (hg : g⁻¹ * a * g = t) : ∃ g' ∈ normalizer (S : Set X), g'⁻¹ * a * g' = t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := hSa.isPGroup
  have hCt : conjugate (centralizer ({a} : Set X)) g = centralizer ({t} : Set X) := by
    rw [conjugate_centralizer_singleton, hg]
  have hcardC : Nat.card (centralizer ({t} : Set X)) = Nat.card (centralizer ({a} : Set X)) := by
    rw [← hCt, card_conjugate]
  have hS1 := isSylowIn_of_card hSt hS2 hSa rfl hcardC
  have hS'C : conjugate S g ≤ centralizer ({t} : Set X) := hCt ▸ map_mono hSa.1
  have hS'2 : IsPGroup 2 (conjugate S g) := hS2.map _
  have hS2' := isSylowIn_of_card hS'C hS'2 hSa (card_conjugate S g) hcardC
  obtain ⟨-, R₁, hR₁⟩ := hS1
  obtain ⟨-, R₂, hR₂⟩ := hS2'
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (centralizer ({t} : Set X)) R₂ R₁
  refine ⟨g * (c : X)⁻¹, ?_, ?_⟩
  ·
    have hmap0 : (R₂ : Subgroup ↥(centralizer ({t} : Set X))).map (MulAut.conj c).toMonoidHom =
        (R₁ : Subgroup ↥(centralizer ({t} : Set X))) := by
      rw [← hc]
      rfl
    rw [hR₁, hR₂] at hmap0
    have hle : conjugate S (g * (c : X)⁻¹) ≤ S := by
      intro v hv
      rw [mem_conjugate_iff] at hv
      set w := g * (c : X)⁻¹ * v * (g * (c : X)⁻¹)⁻¹ with hw
      have hm : g⁻¹ * w * g ∈ conjugate S g := by
        rw [mem_conjugate_iff, show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
        exact hv
      have hm' : (⟨g⁻¹ * w * g, hS'C hm⟩ : ↥(centralizer ({t} : Set X))) ∈
          (conjugate S g).subgroupOf (centralizer ({t} : Set X)) := mem_subgroupOf.mpr hm
      have h1 := hmap0 ▸ mem_map_of_mem (MulAut.conj c).toMonoidHom hm'
      have h2 : (c : X) * (g⁻¹ * w * g) * (c : X)⁻¹ ∈ S := mem_subgroupOf.mp h1
      rwa [show (c : X) * (g⁻¹ * w * g) * (c : X)⁻¹ = v by rw [hw]; group] at h2
    have heq : conjugate S (g * (c : X)⁻¹) = S :=
      eq_of_le_of_card_ge hle (by rw [card_conjugate])
    exact mem_normalizer_of_conjugate_eq heq
  · have hct : (c : X) * t = t * c := mem_centralizer_singleton_iff.mp c.2
    calc (g * (c : X)⁻¹)⁻¹ * a * (g * (c : X)⁻¹) = (c : X) * (g⁻¹ * a * g) * (c : X)⁻¹ := by
          group
      _ = t := by rw [hg, hct, mul_inv_cancel_right]

namespace Setting

variable (s : Setting X)

theorem exists_sylow_Dbar : ∃ T : Sylow 2 (s.h.J ⧸ pPrimeCore 2 s.h.J),
    (T : Subgroup _) = (s.h.D.subgroupOf s.h.J).map (QuotientGroup.mk' (pPrimeCore 2 ↥s.h.J)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := s.sylow_D
  refine ⟨R.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.coe_mapSurjective, hR]

theorem not_conj_a_az (hConj : CFSp4Conj) (hComp : CFSp4Comp) (hOut : CFSp4Outer)
    (hCent : CFL2Cent) (hD : CFSp4D) (hA : CFL2A) (hC : CFL2C) (g : X) :
    g⁻¹ * s.h.a * g ≠ s.h.a * (s.toData hConj hComp hOut hCent).z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set d := s.toData hConj hComp hOut hCent with hd
  intro hg
  have hSaz : s.h.S ≤ centralizer ({s.h.a * d.z} : Set X) := by
    intro w hw
    rw [mem_centralizer_singleton_iff]
    calc w * (s.h.a * d.z) = (w * s.h.a) * d.z := by group
      _ = (s.h.a * w) * d.z := by rw [s.h.comm_a hw]
      _ = s.h.a * (w * d.z) := by group
      _ = s.h.a * (d.z * w) := by rw [d.hzS w hw]
      _ = s.h.a * d.z * w := by group
  have hDn : ∀ t ∈ s.h.S, ∀ v ∈ s.h.D, t * v * t⁻¹ ∈ s.h.D := fun t ht v hv =>
    mem_inf.mpr ⟨mul_mem (mul_mem ht (s.h.D_le_S hv)) (inv_mem ht),
      (mem_normalizer_iff.mp (s.h.S_le_normalizer ht) v).mp (s.h.D_le_J hv)⟩
  obtain ⟨g', hg'N, hg'⟩ := exists_normalizer_conj_of_sylow s.hSa hSaz hg
  have hga : g'⁻¹ * s.h.a * g' ≠ s.h.a := by
    rw [hg']
    intro h1
    apply d.z_ne_one
    calc d.z = s.h.a⁻¹ * (s.h.a * d.z) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]
  obtain ⟨-, h8, -⟩ := s.cfl2A_apply hConj hComp hOut hCent hD hA hg'N hga
  have hDP' : s.h.D ⊓ conjugate s.h.P g' = ⊥ := by
    by_contra hne
    obtain ⟨w, hw, hw1, hwZ⟩ := exists_mem_center_of_normal s.h.isPGroup_S
      (inf_le_left.trans s.h.D_le_S)
      (fun t ht v hv => mem_inf.mpr ⟨hDn t ht v (mem_inf.mp hv).1,
        s.conj_mem_conjugate_P hg'N ht (mem_inf.mp hv).2⟩) hne
    obtain ⟨hwD, hwg⟩ := mem_inf.mp hw
    rw [mem_conjugate_iff] at hwg
    have hpZ : ∀ t ∈ s.h.S, t * (g' * w * g'⁻¹) = g' * w * g'⁻¹ * t := by
      intro t ht
      have htg : g'⁻¹ * t * g' ∈ s.h.S := by
        have := (mem_normalizer_iff.mp (inv_mem hg'N) t).mp ht
        rwa [inv_inv] at this
      have h1 := hwZ _ htg
      calc t * (g' * w * g'⁻¹) = g' * ((g'⁻¹ * t * g') * w) * g'⁻¹ := by group
        _ = g' * (w * (g'⁻¹ * t * g')) * g'⁻¹ := by rw [h1]
        _ = g' * w * g'⁻¹ * t := by group
    have hv : g' * w * g'⁻¹ ∈ s.h.P ⊓ centralizer (s.h.S : Set X) :=
      mem_inf.mpr ⟨hwg, mem_centralizer_iff.mpr hpZ⟩
    rw [s.hC] at hv
    rcases eq_one_or_of_mem_zpowers s.h.orderOf_a hv with h1 | h1
    · apply hw1
      calc w = g'⁻¹ * (g' * w * g'⁻¹) * g' := by group
        _ = 1 := by rw [h1]; group
    · have hw' : w = s.h.a * d.z := by
        calc w = g'⁻¹ * (g' * w * g'⁻¹) * g' := by group
          _ = s.h.a * d.z := by rw [h1, hg']
      have haD : s.h.a ∈ s.h.D := by
        have := mul_mem (hw' ▸ hwD) (inv_mem d.hzD)
        rwa [mul_inv_cancel_right] at this
      have := d.hDP ▸ mem_inf.mpr ⟨haD, s.h.a_mem_P⟩
      exact d.a_ne_one (mem_bot.mp this)
  have hcomm : ∀ x ∈ s.h.D, ∀ p ∈ conjugate s.h.P g', x * p = p * x := by
    intro x hx p hp
    have hpS : p ∈ s.h.S := s.conjugate_P_le_S hg'N hp
    have h1 : x * p * x⁻¹ * p⁻¹ ∈ s.h.D ⊓ conjugate s.h.P g' := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · rw [show x * p * x⁻¹ * p⁻¹ = x * (p * x⁻¹ * p⁻¹) by group]
        exact mul_mem hx (hDn p hpS _ (inv_mem hx))
      · rw [show x * p * x⁻¹ * p⁻¹ = (x * p * x⁻¹) * p⁻¹ by group]
        exact mul_mem (s.conj_mem_conjugate_P hg'N (s.h.D_le_S hx) hp) (inv_mem hp)
    rw [hDP', mem_bot] at h1
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  obtain ⟨T, hT⟩ := s.exists_sylow_Dbar
  have hWN := s.conjugate_P_le_normalizer hg'N
  have hW := s.conjugate_P_inf_kernel hg'N hga
  have hle : rhoImg s.h.J (conjugate s.h.P g') ≤
      centralizer (innOf (T : Subgroup (s.h.J ⧸ pPrimeCore 2 s.h.J)) :
        Set (MulAut (↥s.h.J ⧸ pPrimeCore 2 ↥s.h.J))) := by
    rw [hT, ← rhoImg_eq_innOf s.h.D_le_J]
    rintro _ ⟨⟨p, hpN⟩, hp, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hcomm x (mem_subgroupOf.mp hx) p (mem_subgroupOf.mp hp)
  have hR2 : IsPGroup 2 (rhoImg s.h.J (conjugate s.h.P g')) := by
    have hW2 : IsPGroup 2 (conjugate s.h.P g') :=
      s.h.isPGroup_S.to_le (s.conjugate_P_le_S hg'N)
    exact (hW2.of_equiv (subgroupOfEquivOfLe hWN).symm).map _
  have h4 := hC _ s.p s.f s.hp s.hp2 s.hf s.hJLie T (h8 T) _ hR2 hle
  rw [card_rhoImg hWN hW le_rfl, card_conjugate] at h4
  obtain ⟨D₁, hD₁P, -, T', ⟨eT'⟩⟩ := s.exists_D1 hConj hComp hOut hCent hD
  have h5 : Nat.card D₁ ≤ Nat.card s.h.P := Subgroup.card_le_of_le hD₁P
  rw [Nat.card_congr eT'.toEquiv] at h5
  have := h8 T'
  omega

end Setting

end Seven

end CFSG.ComponentClassification.GSThmB
