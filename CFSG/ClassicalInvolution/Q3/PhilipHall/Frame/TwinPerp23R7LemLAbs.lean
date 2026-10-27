module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.AschTight.S19TStmt
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPfLift
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

theorem perm3_normal_trivial (N : Subgroup (Equiv.Perm (Fin 3))) [N.Normal]
    (h : ∀ x ∈ N, x * x = 1) : N = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  by_contra hne
  have hx1 : x ≠ 1 := fun h1 => hne (by rw [h1]; exact Subgroup.one_mem _)
  have key : ∀ x : Equiv.Perm (Fin 3), x ≠ 1 → x * x = 1 →
      ∃ y : Equiv.Perm (Fin 3), (x * (y * x * y⁻¹)) * (x * (y * x * y⁻¹)) ≠ 1 := by decide +kernel
  obtain ⟨y, hy⟩ := key x hx1 (h x hx)
  have hxy : x * (y * x * y⁻¹) ∈ N :=
    N.mul_mem hx (Subgroup.Normal.conj_mem inferInstance x hx y)
  exact hy (h _ hxy)

theorem perm3_sq_of_pow_two (s : Equiv.Perm (Fin 3)) (k : ℕ) (h : s ^ (2 ^ k) = 1) :
    s * s = 1 := by
  have h3 : ∀ s : Equiv.Perm (Fin 3), s ^ 3 = 1 ∨ s * s = 1 := by decide +kernel
  rcases h3 s with h3 | h3
  · have hd : orderOf s ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    have hd2 : orderOf s ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h
    have h4 : orderOf s ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd hd hd2
    have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by norm_num)
    rw [hcop] at h4
    have : s = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
    simp [this]
  · exact h3

section ModS3

variable {E : Type} [Group E]

@[expose] def ModS3O (E : Type) [Group E] : Prop :=
  ∃ π : E →* Equiv.Perm (Fin 3), Function.Surjective π ∧ classicalInvolutionOddCore E ≤ π.ker ∧
    ∀ x ∈ π.ker, ∃ k : ℕ, x ^ (2 ^ k) ∈ classicalInvolutionOddCore E

theorem ModS3O.of_mulEquiv {E' : Type} [Group E'] (e : E ≃* E') (h : ModS3O E) : ModS3O E' := by
  obtain ⟨π, hs, hO, h2⟩ := h
  have hOe : (classicalInvolutionOddCore E).map e.toMonoidHom = classicalInvolutionOddCore E' :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  refine ⟨π.comp e.symm.toMonoidHom, hs.comp e.symm.surjective, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hOe ▸ hx
    simpa using hO hy
  · intro x hx
    have hx' : e.symm x ∈ π.ker := by rw [MonoidHom.mem_ker]; exact hx
    obtain ⟨k, hk⟩ := h2 _ hx'
    refine ⟨k, ?_⟩
    rw [← hOe]
    refine ⟨_, hk, ?_⟩
    simp [map_pow]

end ModS3

section Ea

variable {G : Type} [Group G]

@[expose] def Ea (Φ : Set (Subgroup G)) (a : G) : Subgroup G :=
  ⨆ L ∈ Φ, ⨆ (_ : L ≤ Subgroup.centralizer ({a} : Set G)), L

theorem le_Ea {Φ : Set (Subgroup G)} {a : G} {L : Subgroup G} (hL : L ∈ Φ)
    (h : L ≤ Subgroup.centralizer ({a} : Set G)) : L ≤ Ea Φ a :=
  le_iSup₂_of_le L hL (le_iSup_of_le h le_rfl)

theorem Ea_le {Φ : Set (Subgroup G)} {a : G} {H : Subgroup G}
    (h : ∀ L ∈ Φ, L ≤ Subgroup.centralizer ({a} : Set G) → L ≤ H) : Ea Φ a ≤ H :=
  iSup₂_le fun L hL => iSup_le fun hLa => h L hL hLa

theorem Ea_le_centralizer (Φ : Set (Subgroup G)) (a : G) :
    Ea Φ a ≤ Subgroup.centralizer ({a} : Set G) :=
  Ea_le fun _ _ h => h

theorem Ea_map {H : Type} [Group H] (ψ : G →* H) (Φ : Set (Subgroup G)) (a : G)
    (hcent : ∀ L ∈ Φ, L.map ψ ≤ Subgroup.centralizer ({ψ a} : Set H) →
      L ≤ Subgroup.centralizer ({a} : Set G)) :
    Ea ((fun L => L.map ψ) '' Φ) (ψ a) = (Ea Φ a).map ψ := by
  apply le_antisymm
  · refine Ea_le fun M hM hMc => ?_
    obtain ⟨L, hL, rfl⟩ := hM
    exact Subgroup.map_mono (le_Ea hL (hcent L hL hMc))
  · unfold Ea
    rw [Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hLa => ?_
    refine le_Ea ⟨L, hL, rfl⟩ ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hLa hx)
    rw [← map_mul, ← map_mul, this]

end Ea

section S3Quot

variable {E E' : Type} [Group E] [Group E']

@[expose] def HasS3Quot (E : Type) [Group E] : Prop :=
  ∃ π : E →* Equiv.Perm (Fin 3), Function.Surjective π

theorem HasS3Quot.of_surjective (ρ : E →* E') (hρ : Function.Surjective ρ)
    (h2 : ∀ x ∈ ρ.ker, ∃ k : ℕ, x ^ (2 ^ k) = 1) (h : HasS3Quot E) : HasS3Quot E' := by
  obtain ⟨π, hπ⟩ := h
  have hker : ρ.ker ≤ π.ker := by
    set N : Subgroup (Equiv.Perm (Fin 3)) := ρ.ker.map π with hN
    haveI : N.Normal := Subgroup.Normal.map inferInstance π hπ
    have hN2 : ∀ y ∈ N, y * y = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := h2 x hx
      refine perm3_sq_of_pow_two (π x) k ?_
      rw [← map_pow, hk, map_one]
    have hbot : N = ⊥ := perm3_normal_trivial N hN2
    intro x hx
    have hxN : π x ∈ N := ⟨x, hx, rfl⟩
    rw [hbot] at hxN
    exact hxN
  refine ⟨MonoidHom.liftOfSurjective ρ hρ ⟨π, hker⟩, ?_⟩
  intro s
  obtain ⟨x, rfl⟩ := hπ s
  exact ⟨ρ x, MonoidHom.liftOfRightInverse_comp_apply ρ _ _ ⟨π, hker⟩ x⟩

end S3Quot

theorem modS3O_of_sup {E : Type} [Group E] [Finite E] (M : Subgroup E)
    (hM : M ⊔ classicalInvolutionOddCore E = ⊤) (π : ↥M →* Equiv.Perm (Fin 3))
    (hπs : Function.Surjective π)
    (hN : ∀ m : ↥M, (m : E) ∈ classicalInvolutionOddCore E → π m = 1)
    (h2 : ∀ m : ↥M, π m = 1 → ∃ k : ℕ, (m : E) ^ (2 ^ k) ∈ classicalInvolutionOddCore E) :
    ModS3O E := by
  set N := classicalInvolutionOddCore E with hNdef
  let f : ↥M →* E ⧸ N := (QuotientGroup.mk' N).comp M.subtype
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hx : x ∈ M ⊔ N := hM ▸ Subgroup.mem_top x
    obtain ⟨m, hm, n, hn, hmn⟩ := Subgroup.mem_sup_of_normal_right.mp hx
    refine ⟨⟨m, hm⟩, ?_⟩
    have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    show QuotientGroup.mk' N m = QuotientGroup.mk' N x
    rw [← hmn, map_mul, hn1, mul_one]
  have hker : f.ker ≤ π.ker := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm ⊢
    have h1 : QuotientGroup.mk' N (m : E) = 1 := hm
    exact hN m ((QuotientGroup.eq_one_iff _).mp h1)
  let ρ : E ⧸ N →* Equiv.Perm (Fin 3) := MonoidHom.liftOfSurjective f hfs ⟨π, hker⟩
  have hρ : ∀ m, ρ (f m) = π m := fun m =>
    MonoidHom.liftOfRightInverse_comp_apply f _ _ ⟨π, hker⟩ m
  refine ⟨ρ.comp (QuotientGroup.mk' N), ?_, ?_, ?_⟩
  · intro s
    obtain ⟨m, rfl⟩ := hπs s
    exact ⟨(m : E), hρ m⟩
  · intro x hx
    rw [MonoidHom.mem_ker]
    show ρ (QuotientGroup.mk' N x) = 1
    have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
    rw [h1, map_one]
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    obtain ⟨m, hm⟩ := hfs (QuotientGroup.mk' N x)
    have hπ1 : π m = 1 := by rw [← hρ, hm]; exact hx
    obtain ⟨k, hk⟩ := h2 m hπ1
    refine ⟨k, ?_⟩
    have hxk : QuotientGroup.mk' N (x ^ 2 ^ k) = 1 := by
      rw [map_pow, ← hm]
      have : (f m) ^ 2 ^ k = f (m ^ 2 ^ k) := (map_pow f m _).symm
      rw [this]
      show QuotientGroup.mk' N (((m ^ 2 ^ k : ↥M) : E)) = 1
      rw [Subgroup.coe_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk
    exact (QuotientGroup.eq_one_iff _).mp hxk

theorem modS3O_of_le_sup {G : Type} [Group G] [Finite G] {M E : Subgroup G} (hME : M ≤ E)
    (hOEn : E ≤ Subgroup.normalizer (oddCoreOf E : Set G)) (hEM : E ≤ oddCoreOf E ⊔ M)
    (π : ↥M →* Equiv.Perm (Fin 3)) (hπs : Function.Surjective π)
    (hN : ∀ m : ↥M, (m : G) ∈ oddCoreOf E → π m = 1)
    (h2 : ∀ m : ↥M, π m = 1 → ∃ k : ℕ, (m : G) ^ (2 ^ k) ∈ oddCoreOf E) : ModS3O ↥E := by
  let g' : ↥(M.subgroupOf E) →* Equiv.Perm (Fin 3) :=
    π.comp (Subgroup.subgroupOfEquivOfLe hME).toMonoidHom
  refine modS3O_of_sup (M.subgroupOf E) ?_ g' ?_ ?_ ?_
  · refine eq_top_iff.mpr fun x _ => ?_
    have hx : (x : G) ∈ ((oddCoreOf E ⊔ M : Subgroup G) : Set G) := hEM x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hME.trans hOEn)] at hx
    obtain ⟨o, ho, m, hm, hom⟩ := hx
    obtain ⟨hoE, hoN⟩ := mem_oddCoreOf_iff.mp ho
    have hx' : x = ⟨o, hoE⟩ * ⟨m, hME hm⟩ := Subtype.ext hom.symm
    rw [hx', sup_comm]
    exact Subgroup.mul_mem_sup hoN (Subgroup.mem_subgroupOf.mpr hm)
  · intro s
    obtain ⟨m, hm⟩ := hπs s
    exact ⟨⟨⟨(m : G), hME m.2⟩, Subgroup.mem_subgroupOf.mpr m.2⟩, hm⟩
  · intro m' hmN
    have hmO : ((m' : ↥E) : G) ∈ oddCoreOf E := mem_oddCoreOf_iff.mpr ⟨(m' : ↥E).2, hmN⟩
    exact hN (Subgroup.subgroupOfEquivOfLe hME m') hmO
  · intro m' hg1
    obtain ⟨k, hk⟩ := h2 (Subgroup.subgroupOfEquivOfLe hME m') hg1
    refine ⟨k, ?_⟩
    obtain ⟨hmE', hmN⟩ := mem_oddCoreOf_iff.mp hk
    have hpow : ((m' : ↥E) ^ 2 ^ k : ↥E) = ⟨((m' : ↥E) : G) ^ 2 ^ k, hmE'⟩ :=
      Subtype.ext (by simp)
    show ((m' : ↥E) ^ 2 ^ k : ↥E) ∈ classicalInvolutionOddCore ↥E
    rw [hpow]
    exact hmN

theorem center_pow_two {G : Type} [Group G] [Finite G] (hO : classicalInvolutionOddCore G = ⊥)
    {x : G} (hx : x ∈ Subgroup.center G) : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  have hn0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hn0
  refine ⟨a, ?_⟩
  set y : G := x ^ (2 ^ a) with hy
  have hdvd : 2 ^ a ∣ orderOf x := ⟨m, hn⟩
  have hord : orderOf y = m := by
    rw [hy, orderOf_pow_of_dvd (by positivity : 2 ^ a ≠ 0) hdvd, hn]
    exact Nat.mul_div_cancel_left m (by positivity)
  have hyc : y ∈ Subgroup.center G := Subgroup.pow_mem _ hx _
  have hnorm : (Subgroup.zpowers y).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hk : y ^ k ∈ Subgroup.center G := Subgroup.zpow_mem _ hyc _
    have := Subgroup.mem_center_iff.mp hk g
    have e : g * y ^ k * g⁻¹ = y ^ k := by rw [this, mul_inv_cancel_right]
    rw [e]
    exact Subgroup.zpow_mem_zpowers y k
  have hodd : Odd (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers, hord]; exact hm
  have hle := CFSG.ComponentClassification.OddCore.maximal G (Subgroup.zpowers y) hnorm hodd
  have hyO : y ∈ classicalInvolutionOddCore G := hle (Subgroup.mem_zpowers y)
  rw [hO, Subgroup.mem_bot] at hyO
  exact hyO

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
