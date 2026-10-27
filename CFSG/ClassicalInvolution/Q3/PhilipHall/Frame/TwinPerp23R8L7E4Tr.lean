module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7E4Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLE4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitE4Base

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

section Tr

variable {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)}

theorem twin_le_normalizer (F : Q8Pre G Φ) {K K' : Subgroup G} (hK : K ∈ Φ) (hK' : K' ∈ Φ)
    (hne : K' ≠ K) {z : G} (hz : IsUniqueInvolution K z) (hz' : IsUniqueInvolution K' z) :
    K' ≤ Subgroup.normalizer (K : Set G) :=
  Sec6Gen.le_normalizer_of_twin F.hyp hK' hK hne hz' hz

theorem isSolvable_of_ker_pow_two {A B : Type} [Group A] [Finite A] [Group B] (ρ : A →* B)
    (h2 : ∀ x ∈ ρ.ker, ∃ k : ℕ, x ^ (2 ^ k) = 1) (hB : Group.IsSolvable B) :
    Group.IsSolvable A := by
  haveI := hB
  have hK : IsPGroup 2 ↥ρ.ker := fun x => by
    obtain ⟨k, hk⟩ := h2 x x.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  haveI : Group.IsNilpotent ↥ρ.ker := IsPGroup.isNilpotent hK
  exact Group.isSolvable_of_ker_le_range ρ.ker.subtype ρ (by simp)

theorem map_le_centralizer_singleton {H : Type} [Group H] (ψ : G →* H) {L : Subgroup G} {a : G}
    (h : L ≤ Subgroup.centralizer ({a} : Set G)) :
    L.map ψ ≤ Subgroup.centralizer ({ψ a} : Set H) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
    Subgroup.mem_centralizer_singleton_iff.mp (h hx)]

theorem Ea_quotFamily {N : Subgroup G} [N.Normal] (c : CentQuotGen Φ N) (a : G) :
    Ea (quotFamily Φ N) (QuotientGroup.mk' N a) = (Ea Φ a).map (QuotientGroup.mk' N) :=
  LemL.Ea_map (QuotientGroup.mk' N) Φ a fun L hL hLc => LemL.centralizes_of_map c hL hLc

theorem not_isSolvable_Ea_quotFamily {N : Subgroup G} [N.Normal] (c : CentQuotGen Φ N)
    (hN2 : IsPGroup 2 ↥N) {a : G} (ha : ¬ Group.IsSolvable ↥(Ea Φ a)) :
    ¬ Group.IsSolvable ↥(Ea (quotFamily Φ N) (QuotientGroup.mk' N a)) := by
  rw [Ea_quotFamily c a]
  intro hs
  refine ha (isSolvable_of_ker_pow_two ((QuotientGroup.mk' N).subgroupMap (Ea Φ a)) (fun x hx => ?_) hs)
  have h1 : QuotientGroup.mk' N (x : G) = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    simpa using this
  have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨k, hk⟩ := hN2 ⟨(x : G), hxN⟩
  refine ⟨k, Subtype.ext ?_⟩
  have := congrArg (fun y : ↥N => (y : G)) hk
  simpa using this

theorem twin_clause_map (F : Q8Pre G Φ) {N : Subgroup G} [N.Normal] (hNc : N ≤ Subgroup.center G)
    {K : Subgroup G} (hK : K ∈ Φ) {z : G} (hz : IsUniqueInvolution K z) :
    ∀ c ∈ Subgroup.centralizer ({QuotientGroup.mk' N z} : Set (G ⧸ N)),
      conjSub c (K.map (QuotientGroup.mk' N)) = K.map (QuotientGroup.mk' N) ∨
        ∀ x ∈ K.map (QuotientGroup.mk' N), ∀ y ∈ conjSub c (K.map (QuotientGroup.mk' N)),
          x * y = y * x := by
  have hnab := TwinDisc.ExitE4.exists_noncomm F.hyp F.two hK
  intro cb hcb
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective N cb
  have hc' : QuotientGroup.mk' N c * QuotientGroup.mk' N z =
      QuotientGroup.mk' N z * QuotientGroup.mk' N c :=
    Subgroup.mem_centralizer_singleton_iff.mp hcb
  have hq : z⁻¹ * (c * z * c⁻¹) ∈ N := by
    have h0 : QuotientGroup.mk' N (z⁻¹ * (c * z * c⁻¹)) = 1 := by
      simp only [map_mul, map_inv]
      rw [hc', mul_inv_cancel_right, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff _).mp h0
  have hcen : ∀ y : G, y * (z⁻¹ * (c * z * c⁻¹)) = (z⁻¹ * (c * z * c⁻¹)) * y :=
    Subgroup.mem_center_iff.mp (hNc hq)
  rcases TwinDisc.ExitE4.twin_clause_central F.hyp F.two hK hz hnab rfl hcen with h | h
  · left
    rw [← AscQuot.map_conjSub, h]
  · right
    rintro _ ⟨x, hx, rfl⟩ y hy
    rw [← AscQuot.map_conjSub] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    rw [← map_mul, ← map_mul, h x hx y' hy']

theorem false_of_twinE4_lay (hmodel : E4TwinLayModel) (F : Q8Pre G Φ) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ Φ) {t₁ : G} (ht₁ : IsUniqueInvolution K₁ t₁) (hno : ¬ TightInO2 t₁)
    (hE : TwinE4 G) {K K' : Subgroup G} (hK : K ∈ Φ) (hK' : K' ∈ Φ) {z : G}
    (hz : IsUniqueInvolution K z) (hne : K' ≠ K) (hle : K' ≤ Subgroup.normalizer (K : Set G))
    (hperp : ∀ J ∈ Φ, J ≠ K → J ≤ Subgroup.normalizer (K : Set G) → J = K')
    {a b : G} (ha : a ∉ Subgroup.center G) (hb : b ∉ Subgroup.center G)
    (hab : a⁻¹ * b ∉ Subgroup.center G)
    (haK : K ≤ Subgroup.centralizer ({a} : Set G)) (haK' : K' ≤ Subgroup.centralizer ({a} : Set G))
    (hbK : K ≤ Subgroup.centralizer ({b} : Set G)) (hbK' : K' ≤ Subgroup.centralizer ({b} : Set G))
    (hna : ¬ Group.IsSolvable ↥(Ea Φ a)) (hnb : ¬ Group.IsSolvable ↥(Ea Φ b))
    (h2 : ∀ x ∈ Ea Φ a, ∃ k : ℕ, (x * b * x⁻¹ * b⁻¹) ^ (2 ^ k) = 1) : False := by
  obtain ⟨Q, hQ, f, hfs, hker, hM⟩ := hE
  have hN2 : IsPGroup 2 ↥f.ker := hker
  have hzN : ∀ J ∈ Φ, ∀ u : G, IsUniqueInvolution J u → u ∉ f.ker := by
    intro J hJ u hu huN
    obtain ⟨g, rfl⟩ := F.trans K₁ hK₁ J hJ
    have hu' : g * t₁ * g⁻¹ = u := (ht₁.conj g).eq hu
    apply hno
    refine ⟨f.ker, inferInstance, hN2, ?_⟩
    have h3 := (inferInstance : f.ker.Normal).conj_mem u huN g⁻¹
    rw [← hu'] at h3
    simpa [mul_assoc] using h3
  have hmeet : ∀ J ∈ Φ, J ⊓ f.ker = ⊥ := fun J hJ => TwinDisc.ExitE4.inf_eq_bot F.two F.hyp hzN hJ
  have hNc : f.ker ≤ Subgroup.center G :=
    TwinDisc.ExitE4.center_of_meet F.hyp F.two F.gen hN2 hmeet
  have hc : CentQuotGen Φ f.ker := TwinDisc.ExitE4.centQuotGen F.hyp F.two hNc hmeet
  have hΦ : CoreAssembly.conjClass K = Φ := LemL.conjClass_eq F hK
  let e : (G ⧸ f.ker) ≃* Q := QuotientGroup.quotientKerEquivOfSurjective f hfs
  have hMq : CFSG.Blueprint.LieModel (G ⧸ f.ker) .PSp 3 2 1 ∨
      CFSG.Blueprint.LieModel (G ⧸ f.ker) .POmegaPlus 4 2 1 :=
    hM.imp (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
      (fun h => CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm h)
  have hinvK : IsUniqueInvolution (K.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker z) :=
    AscQuot.isUniqueInvolution_map_mk (hmeet K hK) hz
  have hq8K : Nonempty (↥(K.map (QuotientGroup.mk' f.ker)) ≃* QuaternionGroup 2) := by
    obtain ⟨eK⟩ := F.q8 K hK
    exact ⟨(AscQuot.quotRestrictEquiv (hmeet K hK)).symm.trans eK⟩
  have htw := twin_clause_map F hNc hK hz
  have hqf : quotFamily Φ f.ker = CoreAssembly.conjClass (K.map (QuotientGroup.mk' f.ker)) := by
    rw [← hΦ]
    exact QuaternionBridge.image_conjClass K
  have hK'cls : K'.map (QuotientGroup.mk' f.ker) ∈
      CoreAssembly.conjClass (K.map (QuotientGroup.mk' f.ker)) := by
    rw [← hqf]
    exact map_mem_quotFamily hK'
  have hK'ne : K'.map (QuotientGroup.mk' f.ker) ≠ K.map (QuotientGroup.mk' f.ker) :=
    hc.map_ne_of_ne hK hK' hne
  have hK'le : K'.map (QuotientGroup.mk' f.ker) ≤
      Subgroup.normalizer ((K.map (QuotientGroup.mk' f.ker) : Subgroup (G ⧸ f.ker)) :
        Set (G ⧸ f.ker)) := by
    rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.le_normalizer_map _ ⟨u, hle hu, rfl⟩
  have hperp' : ∀ J ∈ CoreAssembly.conjClass (K.map (QuotientGroup.mk' f.ker)),
      J ≠ K.map (QuotientGroup.mk' f.ker) →
      J ≤ Subgroup.normalizer ((K.map (QuotientGroup.mk' f.ker) : Subgroup (G ⧸ f.ker)) :
        Set (G ⧸ f.ker)) → J = K'.map (QuotientGroup.mk' f.ker) := by
    intro J hJ hJne hJle
    rw [← hqf] at hJ
    obtain ⟨J₀, hJ₀, rfl⟩ := hJ
    have hJ₀ne : J₀ ≠ K := fun h => hJne (by rw [h])
    have hJ₀le : J₀ ≤ Subgroup.normalizer (K : Set G) := fun u hu =>
      hc.normalizer_of_map K hK u (hJle (Subgroup.mem_map_of_mem _ hu))
    rw [hperp J₀ hJ₀ hJ₀ne hJ₀le]
  have hπa : QuotientGroup.mk' f.ker a ≠ 1 := fun h =>
    ha (hNc ((QuotientGroup.eq_one_iff _).mp h))
  have hπb : QuotientGroup.mk' f.ker b ≠ 1 := fun h =>
    hb (hNc ((QuotientGroup.eq_one_iff _).mp h))
  have hπab : QuotientGroup.mk' f.ker a ≠ QuotientGroup.mk' f.ker b := by
    intro h
    have h0 : QuotientGroup.mk' f.ker (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    exact hab (hNc ((QuotientGroup.eq_one_iff _).mp h0))
  have hnaq : ¬ Group.IsSolvable ↥(Ea (CoreAssembly.conjClass (K.map (QuotientGroup.mk' f.ker)))
      (QuotientGroup.mk' f.ker a)) := by
    rw [← hqf]
    exact not_isSolvable_Ea_quotFamily hc hN2 hna
  have hnbq : ¬ Group.IsSolvable ↥(Ea (CoreAssembly.conjClass (K.map (QuotientGroup.mk' f.ker)))
      (QuotientGroup.mk' f.ker b)) := by
    rw [← hqf]
    exact not_isSolvable_Ea_quotFamily hc hN2 hnb
  obtain ⟨x, hxE, hx1, hx3⟩ := hmodel (G ⧸ f.ker) hMq (K.map (QuotientGroup.mk' f.ker))
    (K'.map (QuotientGroup.mk' f.ker)) (QuotientGroup.mk' f.ker z) hq8K hinvK htw hK'cls hK'ne
    hK'le hperp' (QuotientGroup.mk' f.ker a) (QuotientGroup.mk' f.ker b) hπa hπb hπab
    (map_le_centralizer_singleton _ haK) (map_le_centralizer_singleton _ haK')
    (map_le_centralizer_singleton _ hbK) (map_le_centralizer_singleton _ hbK') hnaq hnbq
  rw [← hqf, Ea_quotFamily hc a] at hxE
  obtain ⟨x₀, hx₀, rfl⟩ := hxE
  obtain ⟨k, hk⟩ := h2 x₀ hx₀
  have hπc : QuotientGroup.mk' f.ker (x₀ * b * x₀⁻¹ * b⁻¹) =
      QuotientGroup.mk' f.ker x₀ * QuotientGroup.mk' f.ker b * (QuotientGroup.mk' f.ker x₀)⁻¹ *
        (QuotientGroup.mk' f.ker b)⁻¹ := by
    simp only [map_mul, map_inv]
  have hk' : (QuotientGroup.mk' f.ker x₀ * QuotientGroup.mk' f.ker b *
      (QuotientGroup.mk' f.ker x₀)⁻¹ * (QuotientGroup.mk' f.ker b)⁻¹) ^ (2 ^ k) = 1 := by
    rw [← hπc, ← map_pow, hk, map_one]
  have hcop : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by norm_num)
  have hgcd := pow_gcd_eq_one.mpr ⟨hx3, hk'⟩
  rw [hcop, pow_one] at hgcd
  exact hx1 hgcd

end Tr

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
