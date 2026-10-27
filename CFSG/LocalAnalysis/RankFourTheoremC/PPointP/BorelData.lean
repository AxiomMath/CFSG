module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointP.Borel
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLift
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointProp31

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointP

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC

section Generic

theorem pow_natCast_of_add {K F : Type*} [Group K] [Field F] (f : F → K)
    (hadd : ∀ s t, f (s + t) = f s * f t) (m : ℕ) (t : F) : f ((m : F) * t) = f t ^ m := by
  have hf0 : f 0 = 1 := by
    have h1 := hadd 0 0
    rw [add_zero] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one (f 0)).symm)
  induction m with
  | zero => rw [Nat.cast_zero, zero_mul, hf0, pow_zero]
  | succ m ih => rw [Nat.cast_succ, add_mul, one_mul, hadd, ih, pow_succ]

theorem mem_zpowers_of_pow_prime_of_isCyclic {D : Type*} [Group D] [Finite D] [IsCyclic D]
    {p : ℕ} [Fact p.Prime] {z c : D} (hz : orderOf z = p) (hc : c ^ p = 1) : c ∈ zpowers z := by
  by_cases hc1 : c = 1
  · rw [hc1]
    exact one_mem _
  have hco : orderOf c = p := orderOf_eq_prime hc hc1
  have h : zpowers z = zpowers c :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by rw [Nat.card_zpowers, Nat.card_zpowers, hz, hco])
  rw [h]
  exact mem_zpowers c

theorem exists_pow_lt_of_mem_zpowers {D : Type*} [Group D] {p : ℕ} [Fact p.Prime] {z c : D}
    (hz : orderOf z = p) (hc : c ∈ zpowers z) : ∃ i : ℕ, i < p ∧ c = z ^ i := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hc
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨(m % p).toNat, ?_, ?_⟩
  · have := Int.emod_lt_of_pos m (show (0 : ℤ) < p by exact_mod_cast (Fact.out : p.Prime).pos)
    omega
  · rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hp0), ← hz, zpow_mod_orderOf]

theorem exists_subgroup_fx_p {G F : Type*} [Group G] [Field F] {p : ℕ} (hp : 0 < p) {x : G}
    (hxp : x ^ p = 1) {f : F → G} (hfadd : ∀ s t, f (s + t) = f s * f t)
    (hfx : ∀ t, f t * x = x * f t) :
    ∃ W : Subgroup G, ∀ g, g ∈ W ↔ ∃ (t : F) (i : ℕ), i < p ∧ g = f t * x ^ i := by
  have hf0 : f 0 = 1 := by
    have h := hfadd 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (mul_one (f 0)).symm)
  have hfneg : ∀ t, f (-t) = (f t)⁻¹ := fun t =>
    eq_inv_of_mul_eq_one_right (by rw [← hfadd, add_neg_cancel, hf0])
  have hxe : ∀ (t : F) (e : ℕ), f t * x ^ e = x ^ e * f t := fun t e =>
    (Commute.pow_right (show Commute (f t) x from hfx t) e).eq
  refine ⟨{ carrier := {g | ∃ (t : F) (i : ℕ), i < p ∧ g = f t * x ^ i}
            mul_mem' := ?_
            one_mem' := ⟨0, 0, hp, by simp [hf0]⟩
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro _ _ ⟨t, i, hi, rfl⟩ ⟨s, j, hj, rfl⟩
    have h1 : f t * x ^ i * (f s * x ^ j) = f (t + s) * x ^ (i + j) := by
      rw [hfadd, pow_add]
      calc f t * x ^ i * (f s * x ^ j) = f t * (x ^ i * f s) * x ^ j := by group
        _ = f t * (f s * x ^ i) * x ^ j := by rw [← hxe s i]
        _ = f t * f s * (x ^ i * x ^ j) := by group
    by_cases hij : i + j < p
    · exact ⟨t + s, i + j, hij, h1⟩
    · refine ⟨t + s, i + j - p, by omega, ?_⟩
      rw [h1]
      congr 1
      have : x ^ (i + j) = x ^ (i + j - p) * x ^ p := by
        rw [← pow_add]
        congr 1
        omega
      rw [this, hxp, mul_one]
  · rintro _ ⟨t, i, hi, rfl⟩
    by_cases hi0 : i = 0
    · exact ⟨-t, 0, hp, by simp [hi0, hfneg]⟩
    · refine ⟨-t, p - i, by omega, ?_⟩
      have hxi : (x ^ i)⁻¹ = x ^ (p - i) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_add, Nat.sub_add_cancel hi.le, hxp]
      rw [mul_inv_rev, hxi, ← hfneg]
      exact (hxe (-t) (p - i)).symm

end Generic

variable {G : Type} [Group G] [Finite G]

namespace IsPPoint

theorem exists_borelData_p {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {P : Sylow p G}
    {M : Subgroup G} {x : G} (hloc : D1Local p P M) (h : IsPPoint p P M x)
    {R : Sylow p (RedCent p x)}
    {K : Subgroup (RedCent p x)} {d : TauCeti.ValidLieTypeIndex} {n : ℕ} (hn : 2 ≤ n)
    (hp5 : 5 ≤ p) (hf : PPointFacts p M x R K (.lie d)) (hd : IsLinTwoIndex p n d)
    (hReq : (R : Subgroup (RedCent p x)) =
      (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
        (centralizer ({x} : Set G))).map
          (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p))) :
    ∃ (f : GaloisField p n → G) (W : Subgroup G),
      (∀ s t, f (s + t) = f s * f t) ∧ Function.Injective f ∧ (∀ t, f t * x = x * f t) ∧
      (∀ t, f t ≠ x) ∧ W ≤ (P : Subgroup G) ⊓ centralizer ({x} : Set G) ∧
      (∀ g, g ∈ W ↔ ∃ (t : GaloisField p n) (i : ℕ), i < p ∧ g = f t * x ^ i) ∧
      (∀ y ∈ (P : Subgroup G) ⊓ centralizer ({x} : Set G), y ^ p = 1 → y ∈ W) ∧
      (∀ a : (GaloisField p n)ˣ, ∃ g : G, g * x * g⁻¹ = x ∧
        ∀ t, g * f t * g⁻¹ = f ((a : GaloisField p n) ^ 2 * t)) ∧
      Nonempty (K ≃* PSL2GF p n) ∧
        (∀ t, ∃ hc : f t ∈ centralizer ({x} : Set G),
          QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
            ⟨f t, hc⟩ ∈ (R : Subgroup (RedCent p x)) ⊓ K ∧
          (t ≠ 0 → QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
            ⟨f t, hc⟩ ≠ 1)) ∧
        (∀ k ∈ (R : Subgroup (RedCent p x)) ⊓ K, ∃ (t : GaloisField p n)
          (hc : f t ∈ centralizer ({x} : Set G)),
          QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
            ⟨f t, hc⟩ = k) ∧
        (∀ σ ∈ K, σ ∈ normalizer ((((R : Subgroup (RedCent p x)) ⊓ K : Subgroup (RedCent p x))) :
            Set (RedCent p x)) → ∃ b : (GaloisField p n)ˣ, ∀ (t : GaloisField p n)
          (hc : f t ∈ centralizer ({x} : Set G))
          (hc' : f ((b : GaloisField p n) ^ 2 * t) ∈ centralizer ({x} : Set G)),
          σ * QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
            ⟨f t, hc⟩ * σ⁻¹ = QuotientGroup.mk'
              (primeComplementCore (G := centralizer ({x} : Set G)) p)
              ⟨f ((b : GaloisField p n) ^ 2 * t), hc'⟩) ∧
        (∀ a : (GaloisField p n)ˣ, ∃ τ ∈ K, τ ∈ normalizer ((((R : Subgroup (RedCent p x)) ⊓ K :
            Subgroup (RedCent p x))) : Set (RedCent p x)) ∧ ∀ (t : GaloisField p n)
          (hc : f t ∈ centralizer ({x} : Set G))
          (hc' : f ((a : GaloisField p n) ^ 2 * t) ∈ centralizer ({x} : Set G)),
          τ * QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)
            ⟨f t, hc⟩ * τ⁻¹ = QuotientGroup.mk'
              (primeComplementCore (G := centralizer ({x} : Set G)) p)
              ⟨f ((a : GaloisField p n) ^ 2 * t), hc'⟩) ∧
        (R : Subgroup (RedCent p x)) =
          (((P : Subgroup G) ⊓ centralizer ({x} : Set G)).subgroupOf
            (centralizer ({x} : Set G))).map
            (QuotientGroup.mk' (primeComplementCore (G := centralizer ({x} : Set G)) p)) := by
  classical
  obtain ⟨hzc, hzp⟩ := h.central_xbar hloc
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set O : Subgroup C := primeComplementCore (G := C) p with hO
  set ρ : C →* RedCent p x := QuotientGroup.mk' O with hρ
  set xC : C := ⟨x, mem_centralizer_singleton_iff.2 rfl⟩ with hxC
  set z : RedCent p x := ρ xC with hz
  have hOcop : p.Coprime (Nat.card O) := primeComplementCore_coprime p
  set Qc : Subgroup C := ((P : Subgroup G) ⊓ C).subgroupOf C with hQc
  have hQcp : IsPGroup p Qc :=
    (P.isPGroup'.to_le (inf_le_left : (P : Subgroup G) ⊓ C ≤ P)).comap_subtype
  have hinj := injOn_mk_of_isPGroup hOcop hQcp
  have hxQ : xC ∈ Qc := mem_subgroupOf.mpr ⟨h.mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hKn : K.Normal := hf.red.normal
  obtain ⟨eK⟩ := hf.equiv
  obtain ⟨eP⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  obtain ⟨T, hT⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal R hKn.isSubnormal
  have hn0 : n ≠ 0 := by omega
  have hFcard : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn0
  obtain ⟨fK, hfKinj, hfKadd, hfKmem, hfKsurj, hfKtor, hfKsq⟩ :=
    exists_borelTorusData_p hp2 hFcard (eK.trans eP) T
  have hx3 : x ^ p = 1 := by
    rw [← h.elem.2.1]
    exact pow_orderOf_eq_one x
  have hxPC : x ∈ (P : Subgroup G) ⊓ C := ⟨h.mem, mem_centralizer_singleton_iff.2 rfl⟩
  have hfX : ∀ t, ((fK t : K) : RedCent p x) ∈ (R : Subgroup (RedCent p x)) := fun t => by
    have : ((fK t : K) : RedCent p x) ∈ (T : Subgroup K).map K.subtype := ⟨fK t, hfKmem t, rfl⟩
    rw [hT] at this
    exact this.1
  have hmemR : ∀ t, ((fK t : K) : RedCent p x) ∈ Qc.map ρ := fun t => by
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
    have : ((fK t : K) : RedCent p x) = z := by rw [← hqρ t, hqt]
    rw [← this]
    exact (fK t).2)
  set fG : GaloisField p n → G := fun t => ((q t : C) : G) with hfG
  have hfGadd : ∀ s t, fG (s + t) = fG s * fG t := fun s t => by
    simp only [hfG, hqadd]
    rfl
  have hfGinj : Function.Injective fG := fun s t hst => by
    have h1 : q s = q t := Subtype.ext hst
    have h2 : ((fK s : K) : RedCent p x) = fK t := by rw [← hqρ s, ← hqρ t, h1]
    exact hfKinj (Subtype.ext h2)
  have hfGx : ∀ t, fG t * x = x * fG t := fun t => congrArg Subtype.val (hqx t)
  have hfGne : ∀ t, fG t ≠ x := fun t ht => hqne t (Subtype.ext ht)
  have hfGQ : ∀ t, fG t ∈ (P : Subgroup G) ⊓ C := fun t => mem_subgroupOf.mp (hqQ t)
  obtain ⟨W, hW⟩ := exists_subgroup_fx_p hp.out.pos hx3 hfGadd hfGx
  have hWQ : W ≤ (P : Subgroup G) ⊓ C := by
    intro g hg
    obtain ⟨t, i, -, rfl⟩ := (hW g).mp hg
    exact ((P : Subgroup G) ⊓ C).mul_mem (hfGQ t) (pow_mem hxPC i)
  set W' : Subgroup C := W.subgroupOf C with hW'
  have hW'Q : W' ≤ Qc := fun w hw => mem_subgroupOf.mpr (hWQ (mem_subgroupOf.mp hw))
  have hW'p : IsPGroup p W' := hQcp.to_le hW'Q
  have hW'mem : ∀ w : C, w ∈ W' ↔ ∃ (t : GaloisField p n) (i : ℕ), i < p ∧ w = q t * xC ^ i := by
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
  have hρw : ∀ (t : GaloisField p n) (i : ℕ),
      ρ (q t * xC ^ i) = ((fK t : K) : RedCent p x) * z ^ i :=
    fun t i => by rw [map_mul, map_pow, hqρ]
  have hfKcomm : ∀ s u : GaloisField p n, ((fK s : K) : RedCent p x) * (fK u : K) =
      (fK u : K) * (fK s : K) := fun s u => by
    have := congrArg (Subtype.val : K → RedCent p x) (show fK s * fK u = fK u * fK s by
      rw [← hfKadd, ← hfKadd, add_comm])
    simpa using this
  have htor : ∀ a : (GaloisField p n)ˣ, ∃ g : G, g * x * g⁻¹ = x ∧
      ∀ t, g * fG t * g⁻¹ = fG ((a : GaloisField p n) ^ 2 * t) := by
    intro a
    obtain ⟨τ, hτN, hτ⟩ := hfKtor a
    obtain ⟨γ, hγ⟩ := QuotientGroup.mk'_surjective O ((τ : K) : RedCent p x)
    have hτX : ∀ t, ((τ : K) : RedCent p x) * ((fK t : K) : RedCent p x) *
        ((τ : K) : RedCent p x)⁻¹ = ((fK ((a : GaloisField p n) ^ 2 * t) : K) : RedCent p x) :=
      fun t => by
        have := congrArg (Subtype.val : K → RedCent p x) (hτ t)
        simpa using this
    have hzτ : ∀ i : ℕ, ((τ : K) : RedCent p x) * z ^ i * ((τ : K) : RedCent p x)⁻¹ = z ^ i :=
      fun i => by
        rw [mul_inv_eq_iff_eq_mul]
        exact mem_center_iff.mp (pow_mem hzc i) _
    have hconjρ : ∀ (t : GaloisField p n) (i : ℕ), ρ (γ * (q t * xC ^ i) * γ⁻¹) =
        ρ (q ((a : GaloisField p n) ^ 2 * t) * xC ^ i) := fun t i => by
      rw [map_mul, map_mul, map_inv, hγ, hρw, hρw]
      calc ((τ : K) : RedCent p x) * (((fK t : K) : RedCent p x) * z ^ i) *
            ((τ : K) : RedCent p x)⁻¹
          = (((τ : K) : RedCent p x) * ((fK t : K) : RedCent p x) * ((τ : K) : RedCent p x)⁻¹) *
            (((τ : K) : RedCent p x) * z ^ i * ((τ : K) : RedCent p x)⁻¹) := by group
        _ = _ := by rw [hτX, hzτ]
    have hγW : ∀ w ∈ W', γ * w * γ⁻¹ ∈ O ⊔ W' := by
      intro w hw
      obtain ⟨t, i, hi, rfl⟩ := (hW'mem w).mp hw
      have hw' : q ((a : GaloisField p n) ^ 2 * t) * xC ^ i ∈ W' :=
        (hW'mem _).mpr ⟨_, i, hi, rfl⟩
      have hker : γ * (q t * xC ^ i) * γ⁻¹ *
          (q ((a : GaloisField p n) ^ 2 * t) * xC ^ i)⁻¹ ∈ O := by
        rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker, map_mul, map_inv, hconjρ,
          mul_inv_cancel]
      have := (O ⊔ W').mul_mem (mem_sup_left hker) (mem_sup_right hw')
      rwa [inv_mul_cancel_right] at this
    obtain ⟨o, ho, w₀, hw₀, hnorm⟩ := exists_normalizing_lift hOcop hW'p hγW
    refine ⟨((o * w₀ * γ : C) : G), ?_, fun t => ?_⟩
    · have := mem_centralizer_singleton_iff.mp (o * w₀ * γ).2
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    · have hqW : q t ∈ W' := (hW'mem _).mpr ⟨t, 0, hp.out.pos, by simp⟩
      have hQ1 : (o * w₀ * γ) * q t * (o * w₀ * γ)⁻¹ ∈ Qc := hW'Q (hnorm (q t) hqW)
      obtain ⟨s, j, hj, rfl⟩ := (hW'mem w₀).mp hw₀
      have hρo : ρ o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
      have hτ' : ρ γ = ((τ : K) : RedCent p x) := hγ
      have hρ1 : ρ ((o * (q s * xC ^ j) * γ) * q t * (o * (q s * xC ^ j) * γ)⁻¹) =
          ρ (q ((a : GaloisField p n) ^ 2 * t)) := by
        rw [hqρ]
        simp only [map_mul, map_inv, hρo, hτ', hρw, one_mul, hqρ]
        set Fs : RedCent p x := ((fK s : K) : RedCent p x) with hFs
        set Ft : RedCent p x := ((fK t : K) : RedCent p x) with hFt
        set Fa : RedCent p x := ((fK ((a : GaloisField p n) ^ 2 * t) : K) : RedCent p x) with hFa
        set τX : RedCent p x := ((τ : K) : RedCent p x) with hτXdef
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
  have hz3 : z ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hzp] at this
  have hpF : ((p : ℕ) : GaloisField p n) = 0 := CharP.cast_eq_zero (GaloisField p n) p
  have hfK0 : fK 0 = 1 := by
    have h1 := hfKadd 0 0
    rw [add_zero] at h1
    exact mul_left_cancel (h1.symm.trans (mul_one (fK 0)).symm)
  have hfK3 : ∀ t, (fK t) ^ p = 1 := fun t => by
    rw [← pow_natCast_of_add fK hfKadd p t, hpF, zero_mul, hfK0]
  have hnotouter : ¬ GL83OuterType24 p (TauCeti.CFSGIndex.lie d) := by
    rintro ⟨d', hdd', hcase⟩
    have hdd : d = d' := by injection hdd'
    subst hdd
    rcases hcase with ⟨h3, -⟩ | ⟨-, hsuz⟩
    · omega
    · obtain ⟨q', hq, -⟩ := hd
      rw [hq] at hsuz
      cases hsuz
  have hW3 : ∀ y ∈ (P : Subgroup G) ⊓ C, y ^ p = 1 → y ∈ W := by
    intro y hy hy3
    set yC : C := ⟨y, hy.2⟩ with hyC
    have hyQ : yC ∈ Qc := mem_subgroupOf.mpr hy
    have hy3C : yC ^ p = 1 := Subtype.ext (by simpa [hyC] using hy3)
    have hyR : ρ yC ∈ (R : Subgroup (RedCent p x)) := by
      rw [hReq]
      exact ⟨yC, hyQ, rfl⟩
    have hy3X : (ρ yC) ^ p = 1 := by rw [← map_pow, hy3C, map_one]
    have hinner : ρ yC ∈ K ⊔ centralizer (K : Set (RedCent p x)) := by
      rcases hf.inner with hout | hin
      · exact absurd hout hnotouter
      · exact hin _ hyR hy3X
    obtain ⟨k, hk, c, hc, hkc⟩ := Subgroup.mem_sup_of_normal_left.mp hinner
    have hcR : c ∈ (R : Subgroup (RedCent p x)) := hf.red.centralizer_le_sylow hzc hzp hc
    have hkR : k ∈ (R : Subgroup (RedCent p x)) := by
      have := (R : Subgroup (RedCent p x)).mul_mem hyR ((R : Subgroup (RedCent p x)).inv_mem hcR)
      rwa [← hkc, mul_inv_cancel_right] at this
    have hkT : k ∈ (T : Subgroup K).map K.subtype := by
      rw [hT]
      exact ⟨hkR, hk⟩
    obtain ⟨τ', hτ'T, rfl⟩ := hkT
    obtain ⟨t, rfl⟩ := hfKsurj τ' hτ'T
    have hkc3 : ((fK t : K) : RedCent p x) ^ p = 1 := by
      have := congrArg (Subtype.val : K → RedCent p x) (hfK3 t)
      simpa using this
    have hkc' : ((fK t : K) : RedCent p x) * c = ρ yC := hkc
    have hcomm : ((fK t : K) : RedCent p x) * c = c * ((fK t : K) : RedCent p x) :=
      mem_centralizer_iff.mp hc _ (fK t).2
    have hc3 : c ^ p = 1 := by
      have h1 : (((fK t : K) : RedCent p x) * c) ^ p =
          ((fK t : K) : RedCent p x) ^ p * c ^ p := (Commute.mul_pow hcomm p)
      rw [hkc', hy3X, hkc3, one_mul] at h1
      exact h1.symm
    have hci : ∃ i : ℕ, i < p ∧ c = z ^ i := by
      have : IsCyclic (centralizer (K : Set (RedCent p x))) := hf.isCyclic
      have hzD : z ∈ centralizer (K : Set (RedCent p x)) :=
        mem_centralizer_iff.mpr fun k _ => (mem_center_iff.mp hzc k)
      have hz'ord : orderOf (⟨z, hzD⟩ : centralizer (K : Set (RedCent p x))) = p := by
        rw [Subgroup.orderOf_mk, hzp]
      have hc'3 : (⟨c, hc⟩ : centralizer (K : Set (RedCent p x))) ^ p = 1 := Subtype.ext hc3
      obtain ⟨m, hm⟩ := mem_zpowers_iff.mp
        (mem_zpowers_of_pow_prime_of_isCyclic hz'ord hc'3)
      have hcz : c ∈ zpowers z := ⟨m, by simpa using congrArg Subtype.val hm⟩
      exact exists_pow_lt_of_mem_zpowers hzp hcz
    obtain ⟨i, hi, hci⟩ := hci
    have hyeq : yC = q t * xC ^ i := hinj _ hyQ _ (Qc.mul_mem (hqQ t) (pow_mem hxQ i)) (by
      rw [hρw, ← hkc', hci])
    refine (hW y).mpr ⟨t, i, hi, ?_⟩
    have := congrArg (Subtype.val : C → G) hyeq
    simpa [hyC, hfG] using this
  refine ⟨fG, W, hfGadd, hfGinj, hfGx, hfGne, hWQ, hW, hW3, htor,
    ⟨eK.trans eP⟩, fun t => ⟨(q t).2, ?_, fun ht h1 => ?_⟩, ?_, ?_, ?_, hReq⟩
  · show ρ (q t) ∈ _
    rw [hqρ]
    exact ⟨hfX t, (fK t).2⟩
  · have h2 : ((fK t : K) : RedCent p x) = 1 := by
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
        (s : RedCent p x) ∈ (R : Subgroup (RedCent p x)) ⊓ K := fun s => by
      rw [← hT]
      exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
    have hσT : (⟨σ, hσK⟩ : K) ∈ normalizer ((T : Subgroup K) : Set K) := by
      rw [mem_normalizer_iff]
      intro s
      have := mem_normalizer_iff.mp hσ (s : RedCent p x)
      rw [hTt, hTt]
      simpa using this
    obtain ⟨b, hb⟩ := hfKsq ⟨σ, hσK⟩ hσT
    refine ⟨b, fun t hc hc' => ?_⟩
    have h1 : QuotientGroup.mk' O ⟨fG t, hc⟩ = ((fK t : K) : RedCent p x) := hqρ t
    have h2 : QuotientGroup.mk' O ⟨fG ((b : GaloisField p n) ^ 2 * t), hc'⟩ =
        ((fK ((b : GaloisField p n) ^ 2 * t) : K) : RedCent p x) := hqρ _
    rw [h1, h2]
    have := congrArg (Subtype.val : K → RedCent p x) (hb t)
    simpa using this
  · intro a
    obtain ⟨τ, hτN, hτ⟩ := hfKtor a
    have hTt : ∀ s : K, s ∈ (T : Subgroup K) ↔
        (s : RedCent p x) ∈ (R : Subgroup (RedCent p x)) ⊓ K := fun s => by
      rw [← hT]
      exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
    refine ⟨(τ : RedCent p x), τ.2, ?_, fun t hc hc' => ?_⟩
    · rw [mem_normalizer_iff]
      intro y
      by_cases hyK : y ∈ K
      · have := mem_normalizer_iff.mp hτN ⟨y, hyK⟩
        rw [hTt, hTt] at this
        simpa using this
      · refine ⟨fun hy => absurd hy.2 hyK, fun hy => ?_⟩
        exfalso
        apply hyK
        have hτK : (τ : RedCent p x)⁻¹ * ((τ : RedCent p x) * y * (τ : RedCent p x)⁻¹) *
            (τ : RedCent p x) ∈ K := by
          exact K.mul_mem (K.mul_mem (K.inv_mem τ.2) hy.2) τ.2
        simpa [mul_assoc] using hτK
    · have h1 : QuotientGroup.mk' O ⟨fG t, hc⟩ = ((fK t : K) : RedCent p x) := hqρ t
      have h2 : QuotientGroup.mk' O ⟨fG ((a : GaloisField p n) ^ 2 * t), hc'⟩ =
          ((fK ((a : GaloisField p n) ^ 2 * t) : K) : RedCent p x) := hqρ _
      rw [h1, h2]
      have := congrArg (Subtype.val : K → RedCent p x) (hτ t)
      simpa using this

end IsPPoint

end CFSG.LocalAnalysis.RankFourTheoremC.PPointP
