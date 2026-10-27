module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLinTwo
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLift
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTriple
import CFSG.LocalAnalysis.RankFourTheoremC.PPointBorel

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

structure PPointThreeInputs : Prop where
  h243 : GL83ComponentPCoreTrivial
  h244 : GL83NongenerationList
  hsig : GL83SignalizerAut
  h313 : GL83NormalElementaryRankFour
  hUB : KFactUnitaryBorelMaximal
  hUI : KFactUnitaryInvolution
  hRB : KFactReeBorelMaximal
  hRI : KFactReeInvolution
  hKU9 : KFactUnitaryAutElemRank
  hM11 : KFactM11Three

namespace IsPPoint

variable {M : Subgroup G} {x : G}

theorem exists_borelData_three {P : Sylow 3 G} (hin : PPointThreeInputs) (hS : D1Global G)
    (hD1 : D1For G) (hFC : FullCoreLocality G) (hloc : D1Local 3 P M) (h : IsPPoint 3 P M x) :
    ∃ (n : ℕ) (f : GaloisField 3 n → G) (W : Subgroup G), 3 ≤ n ∧
      (∀ s t, f (s + t) = f s * f t) ∧ Function.Injective f ∧ (∀ t, f t * x = x * f t) ∧
      (∀ t, f t ≠ x) ∧ W ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) ∧
      (∀ g, g ∈ W ↔ ∃ (t : GaloisField 3 n) (i : ℕ), i < 3 ∧ g = f t * x ^ i) ∧
      (∀ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), y ^ 3 = 1 → y ∈ W) ∧
      (∀ a : (GaloisField 3 n)ˣ, ∃ g : G, g * x * g⁻¹ = x ∧
        ∀ t, g * f t * g⁻¹ = f ((a : GaloisField 3 n) ^ 2 * t)) ∧
      ∃ (R : Sylow 3 (RedCent 3 x)) (K : Subgroup (RedCent 3 x)) (d : TauCeti.ValidLieTypeIndex),
        PPointFacts 3 M x R K (.lie d) ∧ IsLinTwoIndex 3 n d ∧ Nonempty (K ≃* PSL2GF 3 n) ∧
        (∀ t, ∃ hc : f t ∈ centralizer ({x} : Set G),
          QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
            ⟨f t, hc⟩ ∈ (R : Subgroup (RedCent 3 x)) ⊓ K ∧
          (t ≠ 0 → QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
            ⟨f t, hc⟩ ≠ 1)) ∧
        (∀ k ∈ (R : Subgroup (RedCent 3 x)) ⊓ K, ∃ (t : GaloisField 3 n)
          (hc : f t ∈ centralizer ({x} : Set G)),
          QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
            ⟨f t, hc⟩ = k) ∧
        (∀ σ ∈ K, σ ∈ normalizer ((((R : Subgroup (RedCent 3 x)) ⊓ K : Subgroup (RedCent 3 x))) :
            Set (RedCent 3 x)) → ∃ b : (GaloisField 3 n)ˣ, ∀ (t : GaloisField 3 n)
          (hc : f t ∈ centralizer ({x} : Set G))
          (hc' : f ((b : GaloisField 3 n) ^ 2 * t) ∈ centralizer ({x} : Set G)),
          σ * QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
            ⟨f t, hc⟩ * σ⁻¹ = QuotientGroup.mk'
              (primeComplementCore (G := centralizer ({x} : Set G)) 3)
              ⟨f ((b : GaloisField 3 n) ^ 2 * t), hc'⟩) ∧
        (∀ a : (GaloisField 3 n)ˣ, ∃ τ ∈ K, τ ∈ normalizer ((((R : Subgroup (RedCent 3 x)) ⊓ K :
            Subgroup (RedCent 3 x))) : Set (RedCent 3 x)) ∧ ∀ (t : GaloisField 3 n)
          (hc : f t ∈ centralizer ({x} : Set G))
          (hc' : f ((a : GaloisField 3 n) ^ 2 * t) ∈ centralizer ({x} : Set G)),
          τ * QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)
            ⟨f t, hc⟩ * τ⁻¹ = QuotientGroup.mk'
              (primeComplementCore (G := centralizer ({x} : Set G)) 3)
              ⟨f ((a : GaloisField 3 n) ^ 2 * t), hc'⟩) ∧
        (R : Subgroup (RedCent 3 x)) =
          (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
            (centralizer ({x} : Set G))).map
            (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) 3)) := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨R, K, d, n, hf, hn, hd, hReq, -⟩ := h.exists_linTwo_three hin.h243 hin.h244 hin.hsig
    hin.h313 hin.hUB hin.hUI hin.hRB hin.hRI hin.hKU9 hin.hM11 hS hD1 hFC hloc
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) 3 with hO
  set ρ : C →* RedCent 3 x := QuotientGroup.mk' O with hρ
  set xC : C := ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ with hxC
  set z : RedCent 3 x := ρ xC with hz
  have hOcop : (3 : ℕ).Coprime (Nat.card O) := primeComplementCore_coprime 3
  set Qc : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQc
  have hQcp : IsPGroup 3 Qc :=
    (P.isPGroup'.to_le (inf_le_left : (P : Subgroup G) ⊓ C ≤ P)).comap_subtype
  have hinj := injOn_mk_of_isPGroup hOcop hQcp
  have hxQ : xC ∈ Qc := mem_subgroupOf.mpr ⟨h.mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hKn : K.Normal := hf.red.normal
  obtain ⟨eK⟩ := hf.equiv
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hn0 : n ≠ 0 := by omega
  have hFcard : Nat.card (GaloisField 3 n) = 3 ^ n := GaloisField.card 3 n hn0
  obtain ⟨fK, hfKinj, hfKadd, hfKmem, hfKsurj, hfKtor, hfKsq⟩ :=
    exists_borelTorusData hFcard (eK.trans eP) T
  have hx3 : x ^ 3 = 1 := by
    rw [← h.elem.2.1]
    exact pow_orderOf_eq_one x
  have hxPC : x ∈ (P : Subgroup G) ⊓ C := ⟨h.mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hfX : ∀ t, ((fK t : K) : RedCent 3 x) ∈ (R : Subgroup (RedCent 3 x)) := fun t => by
    have : ((fK t : K) : RedCent 3 x) ∈ (T : Subgroup K).map K.subtype := ⟨fK t, hfKmem t, rfl⟩
    rw [hT] at this
    exact this.1
  have hmemR : ∀ t, ((fK t : K) : RedCent 3 x) ∈ Qc.map ρ := fun t => by
    rw [← hReq]
    exact hfX t
  choose q hqQ hqρ using fun t => Subgroup.mem_map.mp (hmemR t)
  have hqadd : ∀ s t, q (s + t) = q s * q t := fun s t => by
    refine hinj _ (hqQ _) _ (Qc.mul_mem (hqQ s) (hqQ t)) ?_
    rw [map_mul, hqρ, hqρ, hqρ, hfKadd]
    rfl
  have hzK : z ∉ K := by
    intro hzK
    have hzZ : (⟨z, hzK⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro k
      exact Subtype.ext (mem_center_iff.mp hzc k)
    rw [hf.center_eq_bot, mem_bot] at hzZ
    have : z = 1 := congrArg Subtype.val hzZ
    rw [this, orderOf_one] at hzp
    omega
  have hqx : ∀ t, q t * xC = xC * q t := fun t => by
    refine hinj _ (Qc.mul_mem (hqQ t) hxQ) _ (Qc.mul_mem hxQ (hqQ t)) ?_
    rw [map_mul, map_mul, hqρ]
    exact mem_center_iff.mp hzc _
  have hqne : ∀ t, q t ≠ xC := fun t hqt => hzK (by
    have : ((fK t : K) : RedCent 3 x) = z := by rw [← hqρ t, hqt]
    rw [← this]
    exact (fK t).2)
  set fG : GaloisField 3 n → G := fun t => ((q t : C) : G) with hfG
  have hfGadd : ∀ s t, fG (s + t) = fG s * fG t := fun s t => by
    simp only [hfG, hqadd]
    rfl
  have hfGinj : Function.Injective fG := fun s t hst => by
    have h1 : q s = q t := Subtype.ext hst
    have h2 : ((fK s : K) : RedCent 3 x) = fK t := by rw [← hqρ s, ← hqρ t, h1]
    exact hfKinj (Subtype.ext h2)
  have hfGx : ∀ t, fG t * x = x * fG t := fun t => congrArg Subtype.val (hqx t)
  have hfGne : ∀ t, fG t ≠ x := fun t ht => hqne t (Subtype.ext ht)
  have hfGQ : ∀ t, fG t ∈ (P : Subgroup G) ⊓ C := fun t => mem_subgroupOf.mp (hqQ t)
  obtain ⟨W, hW⟩ := exists_subgroup_fx hx3 hfGadd hfGx
  have hWQ : W ≤ (P : Subgroup G) ⊓ C := by
    intro g hg
    obtain ⟨t, i, -, rfl⟩ := (hW g).mp hg
    exact ((P : Subgroup G) ⊓ C).mul_mem (hfGQ t) (pow_mem hxPC i)
  set W' : Subgroup C := W.subgroupOf C with hW'
  have hW'Q : W' ≤ Qc := fun w hw => mem_subgroupOf.mpr (hWQ (mem_subgroupOf.mp hw))
  have hW'p : IsPGroup 3 W' := hQcp.to_le hW'Q
  have hW'mem : ∀ w : C, w ∈ W' ↔ ∃ (t : GaloisField 3 n) (i : ℕ), i < 3 ∧ w = q t * xC ^ i := by
    intro w
    rw [hW', mem_subgroupOf, hW]
    constructor
    · rintro ⟨t, i, hi, hw⟩
      exact ⟨t, i, hi, Subtype.ext (by simpa [hfG] using hw)⟩
    · rintro ⟨t, i, hi, rfl⟩
      exact ⟨t, i, hi, by
        rw [hfG]
        simp only [Subgroup.coe_mul, Subgroup.coe_pow]
        rfl⟩
  have hρw : ∀ (t : GaloisField 3 n) (i : ℕ),
      ρ (q t * xC ^ i) = ((fK t : K) : RedCent 3 x) * z ^ i :=
    fun t i => by rw [map_mul, map_pow, hqρ]
  have hfKcomm : ∀ s u : GaloisField 3 n, ((fK s : K) : RedCent 3 x) * (fK u : K) =
      (fK u : K) * (fK s : K) := fun s u => by
    have := congrArg (Subtype.val : K → RedCent 3 x) (show fK s * fK u = fK u * fK s by
      rw [← hfKadd, ← hfKadd, add_comm])
    simpa using this
  have htor : ∀ a : (GaloisField 3 n)ˣ, ∃ g : G, g * x * g⁻¹ = x ∧
      ∀ t, g * fG t * g⁻¹ = fG ((a : GaloisField 3 n) ^ 2 * t) := by
    intro a
    obtain ⟨τ, hτN, hτ⟩ := hfKtor a
    obtain ⟨γ, hγ⟩ := QuotientGroup.mk'_surjective O ((τ : K) : RedCent 3 x)
    have hτX : ∀ t, ((τ : K) : RedCent 3 x) * ((fK t : K) : RedCent 3 x) *
        ((τ : K) : RedCent 3 x)⁻¹ = ((fK ((a : GaloisField 3 n) ^ 2 * t) : K) : RedCent 3 x) :=
      fun t => by
        have := congrArg (Subtype.val : K → RedCent 3 x) (hτ t)
        simpa using this
    have hzτ : ∀ i : ℕ, ((τ : K) : RedCent 3 x) * z ^ i * ((τ : K) : RedCent 3 x)⁻¹ = z ^ i :=
      fun i => by
        rw [mul_inv_eq_iff_eq_mul]
        exact mem_center_iff.mp (pow_mem hzc i) _
    have hconjρ : ∀ (t : GaloisField 3 n) (i : ℕ), ρ (γ * (q t * xC ^ i) * γ⁻¹) =
        ρ (q ((a : GaloisField 3 n) ^ 2 * t) * xC ^ i) := fun t i => by
      rw [map_mul, map_mul, map_inv, hγ, hρw, hρw]
      calc ((τ : K) : RedCent 3 x) * (((fK t : K) : RedCent 3 x) * z ^ i) *
            ((τ : K) : RedCent 3 x)⁻¹
          = (((τ : K) : RedCent 3 x) * ((fK t : K) : RedCent 3 x) * ((τ : K) : RedCent 3 x)⁻¹) *
            (((τ : K) : RedCent 3 x) * z ^ i * ((τ : K) : RedCent 3 x)⁻¹) := by group
        _ = _ := by rw [hτX, hzτ]
    have hγW : ∀ w ∈ W', γ * w * γ⁻¹ ∈ O ⊔ W' := by
      intro w hw
      obtain ⟨t, i, hi, rfl⟩ := (hW'mem w).mp hw
      have hw' : q ((a : GaloisField 3 n) ^ 2 * t) * xC ^ i ∈ W' :=
        (hW'mem _).mpr ⟨_, i, hi, rfl⟩
      have hker : γ * (q t * xC ^ i) * γ⁻¹ *
          (q ((a : GaloisField 3 n) ^ 2 * t) * xC ^ i)⁻¹ ∈ O := by
        rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_inv, hconjρ,
          mul_inv_cancel]
      have := (O ⊔ W').mul_mem (mem_sup_left hker) (mem_sup_right hw')
      rwa [inv_mul_cancel_right] at this
    obtain ⟨o, ho, w₀, hw₀, hnorm⟩ := exists_normalizing_lift hOcop hW'p hγW
    refine ⟨((o * w₀ * γ : C) : G), ?_, fun t => ?_⟩
    · have := mem_centralizer_singleton_iff.mp (o * w₀ * γ).2
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    · have hqW : q t ∈ W' := (hW'mem _).mpr ⟨t, 0, by norm_num, by simp⟩
      have hQ1 : (o * w₀ * γ) * q t * (o * w₀ * γ)⁻¹ ∈ Qc := hW'Q (hnorm (q t) hqW)
      obtain ⟨s, j, hj, rfl⟩ := (hW'mem w₀).mp hw₀
      have hρo : ρ o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
      have hτ' : ρ γ = ((τ : K) : RedCent 3 x) := hγ
      have hρ1 : ρ ((o * (q s * xC ^ j) * γ) * q t * (o * (q s * xC ^ j) * γ)⁻¹) =
          ρ (q ((a : GaloisField 3 n) ^ 2 * t)) := by
        rw [hqρ]
        simp only [map_mul, map_inv, hρo, hτ', hρw, one_mul, hqρ]
        set Fs : RedCent 3 x := ((fK s : K) : RedCent 3 x) with hFs
        set Ft : RedCent 3 x := ((fK t : K) : RedCent 3 x) with hFt
        set Fa : RedCent 3 x := ((fK ((a : GaloisField 3 n) ^ 2 * t) : K) : RedCent 3 x) with hFa
        set τX : RedCent 3 x := ((τ : K) : RedCent 3 x) with hτXdef
        calc Fs * z ^ j * τX * Ft * (Fs * z ^ j * τX)⁻¹
            = Fs * z ^ j * (τX * Ft * τX⁻¹) * (z ^ j)⁻¹ * Fs⁻¹ := by group
          _ = Fs * z ^ j * Fa * (z ^ j)⁻¹ * Fs⁻¹ := by rw [hτX]
          _ = Fa := by
            have h1 : z ^ j * Fa = Fa * z ^ j := (mem_center_iff.mp (pow_mem hzc j) Fa).symm
            have h2 : Fs * Fa = Fa * Fs := hfKcomm s _
            calc Fs * z ^ j * Fa * (z ^ j)⁻¹ * Fs⁻¹ = Fs * (z ^ j * Fa) * (z ^ j)⁻¹ * Fs⁻¹ := by
                  group
              _ = Fs * (Fa * z ^ j) * (z ^ j)⁻¹ * Fs⁻¹ := by rw [h1]
              _ = Fs * Fa * Fs⁻¹ := by group
              _ = Fa := by rw [h2]; group
      have hq1 := hinj _ hQ1 _ (hqQ _) hρ1
      have := congrArg (Subtype.val : C → G) hq1
      simpa [hfG] using this
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzp] at this
  have h3F : (3 : GaloisField 3 n) = 0 := by exact_mod_cast CharP.cast_eq_zero (GaloisField 3 n) 3
  have hfK0 : fK 0 = 1 := by
    have h1 := hfKadd 0 0
    rw [add_zero] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one (fK 0)).symm)
  have hfK3 : ∀ t, (fK t) ^ 3 = 1 := fun t => by
    have h1 : t + t + t = 0 := by linear_combination t * h3F
    calc (fK t) ^ 3 = fK t * fK t * fK t := by simp only [pow_succ, pow_zero, one_mul]
      _ = fK (t + t + t) := by rw [hfKadd, hfKadd]
      _ = 1 := by rw [h1, hfK0]
  have hnotouter : ¬ GL83OuterType24 3 (TauCeti.CFSGIndex.lie d) := by
    rintro ⟨d', hdd', hcase⟩
    have hdd : d = d' := by injection hdd'
    subst hdd
    rcases hcase with ⟨-, h2⟩ | ⟨h5, -⟩
    · obtain ⟨q', hq, hqp, -⟩ := hd
      obtain ⟨q'', hq', hqp', -⟩ := h2
      rw [hq] at hq'
      injection hq' with _ hqq
      subst hqq
      omega
    · omega
  have hW3 : ∀ y ∈ (P : Subgroup G) ⊓ C, y ^ 3 = 1 → y ∈ W := by
    intro y hy hy3
    set yC : C := ⟨y, hy.2⟩ with hyC
    have hyQ : yC ∈ Qc := mem_subgroupOf.mpr hy
    have hy3C : yC ^ 3 = 1 := Subtype.ext (by simpa [hyC] using hy3)
    have hyR : ρ yC ∈ (R : Subgroup (RedCent 3 x)) := by
      rw [hReq]
      exact ⟨yC, hyQ, rfl⟩
    have hy3X : (ρ yC) ^ 3 = 1 := by rw [← map_pow, hy3C, map_one]
    have hinner : ρ yC ∈ K ⊔ centralizer (K : Set (RedCent 3 x)) := by
      rcases hf.inner with hout | hin
      · exact absurd hout hnotouter
      · exact hin _ hyR hy3X
    obtain ⟨k, hk, c, hc, hkc⟩ := Subgroup.mem_sup_of_normal_left.mp hinner
    have hcR : c ∈ (R : Subgroup (RedCent 3 x)) := hf.red.centralizer_le_sylow hzc hzp hc
    have hkR : k ∈ (R : Subgroup (RedCent 3 x)) := by
      have := (R : Subgroup (RedCent 3 x)).mul_mem hyR ((R : Subgroup (RedCent 3 x)).inv_mem hcR)
      rwa [← hkc, mul_inv_cancel_right] at this
    have hkT : k ∈ (T : Subgroup K).map K.subtype := by
      rw [hT]
      exact ⟨hkR, hk⟩
    obtain ⟨τ', hτ'T, rfl⟩ := hkT
    obtain ⟨t, rfl⟩ := hfKsurj τ' hτ'T
    have hkc3 : ((fK t : K) : RedCent 3 x) ^ 3 = 1 := by
      have := congrArg (Subtype.val : K → RedCent 3 x) (hfK3 t)
      simpa using this
    have hkc' : ((fK t : K) : RedCent 3 x) * c = ρ yC := hkc
    have hcomm : ((fK t : K) : RedCent 3 x) * c = c * ((fK t : K) : RedCent 3 x) :=
      mem_centralizer_iff.mp hc _ (fK t).2
    have hc3 : c ^ 3 = 1 := by
      have h1 : (((fK t : K) : RedCent 3 x) * c) ^ 3 =
          ((fK t : K) : RedCent 3 x) ^ 3 * c ^ 3 := (Commute.mul_pow hcomm 3)
      rw [hkc', hy3X, hkc3, one_mul] at h1
      exact h1.symm
    have hci : ∃ i : ℕ, i < 3 ∧ c = z ^ i := by
      have : IsCyclic (centralizer (K : Set (RedCent 3 x))) := hf.isCyclic
      have hzD : z ∈ centralizer (K : Set (RedCent 3 x)) :=
        mem_centralizer_iff.mpr fun k _ => (mem_center_iff.mp hzc k)
      have hz'ord : orderOf (⟨z, hzD⟩ : centralizer (K : Set (RedCent 3 x))) = 3 := by
        rw [Subgroup.orderOf_mk, hzp]
      have hc'3 : (⟨c, hc⟩ : centralizer (K : Set (RedCent 3 x))) ^ 3 = 1 := Subtype.ext hc3
      obtain ⟨m, hm⟩ := mem_zpowers_iff.mp
        (mem_zpowers_of_pow_three_of_isCyclic hz'ord hc'3)
      have hcz : c ∈ zpowers z := ⟨m, by simpa using congrArg Subtype.val hm⟩
      rcases mem_zpowers_of_pow_three hz3 hcz with h1 | h1 | h1
      · exact ⟨0, by norm_num, by rw [h1, pow_zero]⟩
      · exact ⟨1, by norm_num, by rw [h1, pow_one]⟩
      · refine ⟨2, by norm_num, ?_⟩
        rw [h1]
        exact (eq_inv_of_mul_eq_one_right (by
          calc z * z ^ 2 = z ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
            _ = 1 := hz3)).symm
    obtain ⟨i, hi, hci⟩ := hci
    have hyeq : yC = q t * xC ^ i := hinj _ hyQ _ (Qc.mul_mem (hqQ t) (pow_mem hxQ i)) (by
      rw [hρw, ← hkc', hci])
    refine (hW y).mpr ⟨t, i, hi, ?_⟩
    have := congrArg (Subtype.val : C → G) hyeq
    simpa [hyC, hfG] using this
  refine ⟨n, fG, W, hn, hfGadd, hfGinj, hfGx, hfGne, hWQ, hW, hW3, htor, R, K, d, hf, hd,
    ⟨eK.trans eP⟩, fun t => ⟨(q t).2, ?_, fun ht h1 => ?_⟩, ?_, ?_, ?_, hReq⟩
  · show ρ (q t) ∈ _
    rw [hqρ]
    exact ⟨hfX t, (fK t).2⟩
  · have h2 : ((fK t : K) : RedCent 3 x) = 1 := by
      rw [← hqρ t]
      exact h1
    exact ht (hfKinj ((Subtype.ext h2).trans hfK0.symm))
  · intro k hk
    have hk' : k ∈ (T : Subgroup K).map K.subtype := by rw [hT]; exact hk
    obtain ⟨k₀, hk₀, rfl⟩ := hk'
    obtain ⟨t, rfl⟩ := hfKsurj k₀ hk₀
    exact ⟨t, (q t).2, hqρ t⟩
  · intro σ hσK hσ
    have hTt : ∀ s : K, s ∈ (T : Subgroup K) ↔
        (s : RedCent 3 x) ∈ (R : Subgroup (RedCent 3 x)) ⊓ K := fun s => by
      rw [← hT]
      exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
    have hσT : (⟨σ, hσK⟩ : K) ∈ normalizer ((T : Subgroup K) : Set K) := by
      rw [mem_normalizer_iff]
      intro s
      have := mem_normalizer_iff.mp hσ (s : RedCent 3 x)
      rw [hTt, hTt]
      simpa using this
    obtain ⟨b, hb⟩ := hfKsq ⟨σ, hσK⟩ hσT
    refine ⟨b, fun t hc hc' => ?_⟩
    have h1 : QuotientGroup.mk' O ⟨fG t, hc⟩ = ((fK t : K) : RedCent 3 x) := hqρ t
    have h2 : QuotientGroup.mk' O ⟨fG ((b : GaloisField 3 n) ^ 2 * t), hc'⟩ =
        ((fK ((b : GaloisField 3 n) ^ 2 * t) : K) : RedCent 3 x) := hqρ _
    rw [h1, h2]
    have := congrArg (Subtype.val : K → RedCent 3 x) (hb t)
    simpa using this
  · intro a
    obtain ⟨τ, hτN, hτ⟩ := hfKtor a
    have hTt : ∀ s : K, s ∈ (T : Subgroup K) ↔
        (s : RedCent 3 x) ∈ (R : Subgroup (RedCent 3 x)) ⊓ K := fun s => by
      rw [← hT]
      exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
    refine ⟨(τ : RedCent 3 x), τ.2, ?_, fun t hc hc' => ?_⟩
    · rw [mem_normalizer_iff]
      intro y
      by_cases hyK : y ∈ K
      · have := mem_normalizer_iff.mp hτN ⟨y, hyK⟩
        rw [hTt, hTt] at this
        simpa using this
      · refine ⟨fun hy => absurd hy.2 hyK, fun hy => ?_⟩
        exfalso
        apply hyK
        have hτK : (τ : RedCent 3 x)⁻¹ * ((τ : RedCent 3 x) * y * (τ : RedCent 3 x)⁻¹) *
            (τ : RedCent 3 x) ∈ K := by
          exact K.mul_mem (K.mul_mem (K.inv_mem τ.2) hy.2) τ.2
        simpa [mul_assoc] using hτK
    · have h1 : QuotientGroup.mk' O ⟨fG t, hc⟩ = ((fK t : K) : RedCent 3 x) := hqρ t
      have h2 : QuotientGroup.mk' O ⟨fG ((a : GaloisField 3 n) ^ 2 * t), hc'⟩ =
          ((fK ((a : GaloisField 3 n) ^ 2 * t) : K) : RedCent 3 x) := hqρ _
      rw [h1, h2]
      have := congrArg (Subtype.val : K → RedCent 3 x) (hτ t)
      simpa using this

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC
