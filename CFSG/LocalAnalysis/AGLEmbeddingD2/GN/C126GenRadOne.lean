module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenComplement
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenNatBlock
import CFSG.Quasithin.Background.C1GNSolvAlt
public import CFSG.Quasithin.Background.F1Models
import CFSG.Quasithin.Background.C126Split

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

theorem radFree_of_complement {H T M V K₁ : Subgroup G} (hmin : MinParabolic H T M)
    (hHN : H ≤ Subgroup.normalizer (V : Set G))
    (hQC : pCoreOf 2 H ≤ Subgroup.centralizer (V : Set G))
    (hCJ : H ⊓ Subgroup.centralizer (V : Set G) ≤ kerIn M H)
    (hK₁K : K₁ ≤ twoResidual H)
    (hdec : ∀ k ∈ twoResidual H, ∃ k₁ ∈ K₁,
      ∃ r ∈ twoResidual H ⊓ Subgroup.centralizer (V : Set G), k = k₁ * r)
    (hK₁C : IsPGroup 2 ↥(K₁ ⊓ Subgroup.centralizer (V : Set G))) :
    twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H := by
  classical
  have hKH : twoResidual H ≤ H := twoResidual_le H
  set RK : Subgroup G := twoResidual H ⊓ Subgroup.centralizer (V : Set G) with hRK
  have hRKH : RK ≤ H := inf_le_left.trans hKH
  set Q' : Subgroup ↥H := CFSG.Open.pCore 2 ↥H with hQ'
  set π : ↥H →* ↥H ⧸ Q' := QuotientGroup.mk' Q' with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hX := hmin.subgroupOf
  have hker : π.ker ≤ M.subgroupOf H := by
    rw [hπ, QuotientGroup.ker_mk']
    exact hX.pCore_le_M
  have hbar := hX.map_of_surjective hπs hker
  have hO : CFSG.Open.pCore 2 (↥H ⧸ Q') = ⊥ := B6.pCore_quotient_pCore
  have hRKn : H ≤ Subgroup.normalizer (RK : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨le_normalizer_twoResidual H hg, B6.le_normalizer_centralizer hHN hg⟩
  have hRn0 : (RK.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRKH).2 hRKn
  have hRn : ((RK.subgroupOf H).map π).Normal := hRn0.map π hπs
  have hJbar : kerIn ((M.subgroupOf H).map π) ⊤ = ((kerIn M H).subgroupOf H).map π := by
    rw [B6.kerIn_map_top hπs hker, B6.kerIn_subgroupOf_top]
  have hRJ : (RK.subgroupOf H).map π ≤ kerIn ((M.subgroupOf H).map π) ⊤ := by
    rw [hJbar]
    refine Subgroup.map_mono fun x hx => ?_
    exact hCJ ⟨hRKH hx, (Subgroup.mem_inf.1 hx).2⟩
  have hnil : Group.IsNilpotent ↥(kerIn ((M.subgroupOf H).map π) ⊤) := hbar.isNilpotent_kerIn hO
  have hRsolv : Group.IsSolvable ↥((RK.subgroupOf H).map π) := by
    have : Group.IsSolvable ↥(kerIn ((M.subgroupOf H).map π) ⊤) := inferInstance
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hRJ)
  have hJodd : Odd (Nat.card ↥(kerIn ((M.subgroupOf H).map π) ⊤)) := by
    have hS := hbar.isSylowTwoOf_pCoreOf_kerIn
    rw [B6.pCoreOf_top, hO] at hS
    have h2 := hS.2.2
    rw [Subgroup.bot_subgroupOf, Subgroup.index_bot] at h2
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2)
  have hRodd : Odd (Nat.card ↥((RK.subgroupOf H).map π)) :=
    hJodd.of_dvd_nat (Subgroup.card_dvd_of_le hRJ)
  have hLbar : twoResidual (⊤ : Subgroup (↥H ⧸ Q')) = ((twoResidual H).subgroupOf H).map π := by
    rw [← B6.twoResidual_map_top hπs, B6.twoResidual_top_eq_subgroupOf]
  have hLn : (twoResidual (⊤ : Subgroup (↥H ⧸ Q'))).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hXs : twoResidual (⊤ : Subgroup (↥H ⧸ Q')) ⊔ (T.subgroupOf H).map π = ⊤ := by
    rw [sup_comm]
    exact sup_twoResidual_eq hbar.isSylow
  have hK₁H : K₁ ≤ H := hK₁K.trans hKH
  have hRC : (RK.subgroupOf H).map π ⊓ (K₁.subgroupOf H).map π = ⊥ := by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨hyR, ⟨z, hzK, hzy⟩⟩ := hy
    obtain ⟨x, hxR, hxy⟩ := hyR
    have hxz : (x : ↥H ⧸ Q') = z := hxy.trans hzy.symm
    have hmem : x⁻¹ * z ∈ Q' := QuotientGroup.eq.1 hxz
    have hmemC : (x : G)⁻¹ * z ∈ Subgroup.centralizer (V : Set G) :=
      hQC ⟨x⁻¹ * z, hmem, rfl⟩
    have hxC : (x : G) ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_subgroupOf.1 hxR).2
    have hzC : (z : G) ∈ Subgroup.centralizer (V : Set G) := by
      have := Subgroup.mul_mem _ hxC hmemC
      simpa using this
    obtain ⟨j, hj⟩ := hK₁C ⟨z, ⟨Subgroup.mem_subgroupOf.1 hzK, hzC⟩⟩
    have hzj' : (z : G) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hzj : z ^ 2 ^ j = 1 := Subtype.ext (by simpa using hzj')
    have hy2 : y ^ 2 ^ j = 1 := by
      rw [← hzy, ← map_pow, hzj, map_one]
    have hyR' : y ∈ (RK.subgroupOf H).map π := ⟨x, hxR, hxy⟩
    have h1 : orderOf (⟨y, hyR'⟩ : ↥((RK.subgroupOf H).map π)) ∣
        Nat.card ↥((RK.subgroupOf H).map π) := orderOf_dvd_natCard _
    have h2 : orderOf (⟨y, hyR'⟩ : ↥((RK.subgroupOf H).map π)) ∣ 2 ^ j :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext hy2)
    have h3 := Nat.eq_one_of_dvd_coprimes ((Nat.coprime_two_left.2 hRodd).pow_left j) h2 h1
    have := orderOf_eq_one_iff.1 h3
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hL : (RK.subgroupOf H).map π ⊔ (K₁.subgroupOf H).map π =
      twoResidual (⊤ : Subgroup (↥H ⧸ Q')) := by
    rw [hLbar]
    apply le_antisymm
    · refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1,
          rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, Subgroup.mem_subgroupOf.2 (hK₁K (Subgroup.mem_subgroupOf.1 hx)), rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k₁, hk₁, r, hr, hkr⟩ := hdec x (Subgroup.mem_subgroupOf.1 hx)
      have hx' : x = ⟨k₁, hK₁H hk₁⟩ * ⟨r, hRKH hr⟩ := Subtype.ext hkr
      rw [hx', map_mul, sup_comm]
      exact Subgroup.mul_mem_sup ⟨_, Subgroup.mem_subgroupOf.2 hk₁, rfl⟩
        ⟨_, Subgroup.mem_subgroupOf.2 hr, rfl⟩
  have key : (RK.subgroupOf H).map π = ⊥ :=
    eq_bot_of_solvable_complement hbar hRsolv hRodd (hRJ.trans kerIn_le) hLn hXs hRC hL
  intro x hx
  have hxH : x ∈ H := hKH hx.1
  have hxbar : π ⟨x, hxH⟩ ∈ (RK.subgroupOf H).map π :=
    ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [key, Subgroup.mem_bot] at hxbar
  exact ⟨⟨x, hxH⟩, (QuotientGroup.eq_one_iff _).1 hxbar, rfl⟩

theorem isPGroup_of_map_eq_bot_or_top {K Γ : Type*} [Group K] [Group Γ] [Finite K]
    (α : K →* Γ) (hker : IsPGroup 2 α.ker) (N : Subgroup K) [N.Normal]
    (hN : N.map α = ⊥ ∨ N.map α = ⊤) (x : K) (hx : ∀ j : ℕ, x ^ 2 ^ j ∉ N) :
    IsPGroup 2 N := by
  rcases hN with h0 | h1
  · exact hker.to_le ((Subgroup.map_eq_bot_iff N).1 h0)
  · exfalso
    obtain ⟨n, hn, hnx⟩ : α x ∈ N.map α := h1 ▸ Subgroup.mem_top _
    have ho : x * n⁻¹ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, mul_inv_cancel]
    obtain ⟨j, hj⟩ := hker ⟨x * n⁻¹, ho⟩
    have hj' : (x * n⁻¹) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    refine hx j ((QuotientGroup.eq_one_iff _).1 ?_)
    have hxn : (QuotientGroup.mk x : K ⧸ N) = QuotientGroup.mk (x * n⁻¹) := by
      rw [QuotientGroup.eq]
      simpa using N.inv_mem hn
    rw [QuotientGroup.mk_pow, hxn, ← QuotientGroup.mk_pow, hj', QuotientGroup.mk_one]

theorem isPGroup_inf_centralizer_of_block {P K₁ V : Subgroup G} {hV : IsElemAbelian 2 V}
    {L : Subgroup (MulAut (IntMod V hV))} {C : Subgroup (IntMod V hV)} {n : ℕ}
    (hBlk : IsL2OrA3Block P K₁) (hPN : P ≤ Subgroup.normalizer (V : Set G))
    (hρ : autI hV K₁ = L) (hnat : E2.IsL2Natural L C n) :
    IsPGroup 2 ↥(K₁ ⊓ Subgroup.centralizer (V : Set G)) := by
  classical
  have hK₁N : K₁ ≤ Subgroup.normalizer (V : Set G) := hBlk.1.2.1.trans hPN
  have hCn : K₁ ≤ Subgroup.normalizer
      ((K₁ ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, B6.le_normalizer_centralizer hK₁N hg⟩
  have hNn : ((K₁ ⊓ Subgroup.centralizer (V : Set G)).subgroupOf K₁).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 hCn
  obtain ⟨k₀, hk₀K, hk₀⟩ : ∃ k₀ ∈ K₁, ∀ j : ℕ,
      k₀ ^ 2 ^ j ∉ Subgroup.centralizer (V : Set G) := by
    have hcard : Nat.card ↥L = 2 ^ n * (4 ^ n - 1) := C126.card_of_isL2Natural hnat
    have h3 : 3 ∣ Nat.card ↥L := by
      rw [hcard]
      refine Dvd.dvd.mul_left ?_ _
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hxL : (x : MulAut (IntMod V hV)) ∈ autI hV K₁ := hρ ▸ x.2
    obtain ⟨g, hgK, hgx⟩ := (mem_autI hV).1 hxL
    refine ⟨(g : G), hgK, fun j hj => ?_⟩
    have h1 : convI hV (g ^ 2 ^ j) = 1 := (convI_eq_one_iff hV _).2 (by simpa using hj)
    rw [map_pow, hgx] at h1
    have h2 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
    rw [hx3] at h2
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2) (by norm_num)
  have hx : ∀ j : ℕ, (⟨k₀, hk₀K⟩ : ↥K₁) ^ 2 ^ j ∉
      (K₁ ⊓ Subgroup.centralizer (V : Set G)).subgroupOf K₁ := fun j hj =>
    hk₀ j (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hj)).2
  have key : IsPGroup 2 ↥((K₁ ⊓ Subgroup.centralizer (V : Set G)).subgroupOf K₁) := by
    rcases hBlk.2 with ⟨n', hn', F, hF, hFin, hcard, α, hαs, hαk, -⟩ | ⟨α, -, hαk, -⟩
    · have hker : IsPGroup 2 α.ker := by
        rw [hαk]
        exact CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K₁) 2
      have hF2 : Nat.card F = 2 ^ n' := by rw [Nat.card_eq_fintype_card]; exact hcard
      have hchar : CharP F 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two (by omega) hF2
      have h4 : 4 ≤ Nat.card F := by
        rw [hF2]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn'
      have hsimple := C126.Nat.isSimpleGroup_sl2 (F := F) h4
      have := hNn.map α hαs
      exact isPGroup_of_map_eq_bot_or_top α hker _
        (hsimple.eq_bot_or_eq_top_of_normal _) ⟨k₀, hk₀K⟩ hx
    · have hker : IsPGroup 2 α.ker := by
        rw [hαk]
        exact CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K₁) 2
      have : Fact (Nat.Prime (Nat.card (alternatingGroup (Fin 3)))) :=
        ⟨by rw [C1GN.alt3_card]; exact Nat.prime_three⟩
      exact isPGroup_of_map_eq_bot_or_top α hker _
        (Subgroup.eq_bot_or_eq_top_of_prime_card _) ⟨k₀, hk₀K⟩ hx
  exact key.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_left)

theorem radFree_of_natCtx_single {H T M V P : Subgroup G} {hV : IsElemAbelian 2 V}
    {I : Finset (Subgroup (MulAut (IntMod V hV)))} (c : NatCtxGen H T M V hV I)
    (hI : I.card < 2) (hSP : baum T ≤ P) (hPK : P ≤ twoResidual H ⊔ baum T) (hPM : ¬ P ≤ M)
    (hMinP : MinParabolic P (baum T) (P ⊓ M)) (hBlk : IsL2OrA3Block P (twoResidual P)) :
    twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H := by
  have hSH : baum T ≤ H := inf_le_left.trans c.min.isSylow.1
  have hPH : P ≤ H := hPK.trans (sup_le (twoResidual_le H) hSH)
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPH.trans c.hHN
  obtain ⟨L, hL, hLP⟩ := c.exists_factor_le_rho hPH hSP hPK hPM hMinP
  have hρ := c.rho_twoResidual_eq hPN hL (c.rho_eq hPH hSP hMinP hL hLP)
  have hone : ∀ L' ∈ I, L' = L := fun L' hL' =>
    Finset.card_le_one.1 (by omega) L' hL' L hL
  obtain ⟨n, -, hnat⟩ := c.nat L hL
  have hKP : twoResidual P ≤ twoResidual H := c.twoResidual_le_K hPK
  have hKL : autI hV (twoResidual H) ≤ L := by
    refine (autI_mono hV c.kj).trans ?_
    rw [c.jeq]
    exact iSup₂_le fun L' hL' => (hone L' hL').le
  refine radFree_of_complement c.min c.hHN (MinParabolic.pCoreOf_le_centralizer c.red)
    (c.min.inf_centralizer_le_kerIn c.red c.not_le_centralizer) hKP ?_
    (isPGroup_inf_centralizer_of_block hBlk hPN hρ hnat)
  intro k hk
  have hkN : k ∈ Subgroup.normalizer (V : Set G) := c.hHN (twoResidual_le H hk)
  have hmem : convI hV ⟨k, hkN⟩ ∈ autI hV (twoResidual P) := by
    rw [hρ]
    exact hKL (convI_mem_autI hV hk hkN)
  obtain ⟨g, hgK, hgk⟩ := (mem_autI hV).1 hmem
  have h1 : convI hV (g⁻¹ * ⟨k, hkN⟩) = 1 := by
    rw [map_mul, map_inv, hgk, inv_mul_cancel]
  have h2 : (g : G)⁻¹ * k ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
  have hrK : (g : G)⁻¹ * k ∈ twoResidual H :=
    (twoResidual H).mul_mem ((twoResidual H).inv_mem (hKP hgK)) hk
  exact ⟨g, hgK, (g : G)⁻¹ * k, ⟨hrK, h2⟩, by group⟩

end CFSG.AGLEmbeddingD2.GN
