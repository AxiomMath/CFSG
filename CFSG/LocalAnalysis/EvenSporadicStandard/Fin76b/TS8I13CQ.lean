module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Cl2

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c

variable {c}

theorem IsRs.exists_good_conj_pt {Rs : Subgroup G} (hR : c.IsRs Rs)
    {y : G} (hy : y ∈ Rs ⊓ c.N1) (hy2 : y * y = 1)
    (hbig : 2 ^ 9 ∣ Nat.card ↥(Subgroup.centralizer
      ({(⟨c.rho ⟨y, hy.2⟩, ⟨⟨y, hy.2⟩, rfl⟩⟩ : ↥c.rho.range)} : Set ↥c.rho.range))) :
    ∃ y' : G, ∃ hy' : y' ∈ Rs ⊓ c.N1, (∃ n ∈ c.N1, y' = n * y * n⁻¹) ∧
      2 ^ 9 ≤ Nat.card ↥(c.Rhat (Rs ⊓ c.N1) ⊓
        centralizer ({c.rho ⟨y', hy'.2⟩} : Set (MulAut ↥E × MulAut ↥E))) := by
  classical
  set R : Subgroup G := Rs ⊓ c.N1 with hRdef
  set Rh : Subgroup (MulAut ↥E × MulAut ↥E) := c.Rhat R with hRh
  have hRN : R ≤ c.N1 := inf_le_right
  let P : Subgroup c.rho.range := Rh.subgroupOf c.rho.range
  have hP : IsPGroup 2 P := (c.Rhat_pgroup hR.R_pgroup).comap_subtype (K := c.rho.range)
  have hPmax : ∀ Q : Subgroup c.rho.range, IsPGroup 2 Q → P ≤ Q → Q = P := by
    intro Q hQ hPQ
    have hQ' : IsPGroup 2 (Q.map c.rho.range.subtype) := hQ.map _
    have hQle : Q.map c.rho.range.subtype ≤ c.rho.range := by
      rintro _ ⟨q, -, rfl⟩
      exact q.2
    have hRhQ : Rh ≤ Q.map c.rho.range.subtype := by
      intro x hx
      have hxr : (⟨x, c.Rhat_le_range R hx⟩ : ↥c.rho.range) ∈ P := mem_subgroupOf.2 hx
      exact ⟨⟨x, c.Rhat_le_range R hx⟩, hPQ hxr, rfl⟩
    have hle := hR.Rhat_max (Q.map c.rho.range.subtype) hQ' hQle hRhQ
    refine le_antisymm ?_ hPQ
    intro q hq
    exact mem_subgroupOf.2 (hle ⟨q, hq, rfl⟩)
  have hyN : y ∈ c.N1 := hy.2
  have hψ0 : c.rho ⟨y, hyN⟩ * c.rho ⟨y, hyN⟩ = 1 := by
    rw [← map_mul, ← map_one c.rho]
    congr 1
    exact Subtype.ext hy2
  let ψ : ↥c.rho.range := ⟨c.rho ⟨y, hyN⟩, ⟨⟨y, hyN⟩, rfl⟩⟩
  have hψ : ψ * ψ = 1 := Subtype.ext hψ0
  obtain ⟨g, hgP, hgC⟩ := exists_conj_mem_sylow_big_cent hP hPmax hψ hbig
  obtain ⟨n, hn⟩ := MonoidHom.mem_range.1 g.2
  set y₁ : G := (n : G) * y * (n : G)⁻¹ with hy₁def
  have hy₁N : y₁ ∈ c.N1 := mul_mem (mul_mem n.2 hyN) (inv_mem n.2)
  set sg : MulAut ↥E × MulAut ↥E := (g * ψ * g⁻¹ : ↥c.rho.range).1 with hsgdef
  have hρy₁ : c.rho ⟨y₁, hy₁N⟩ = sg := by
    show c.rho (n * ⟨y, hyN⟩ * n⁻¹) = _
    rw [map_mul, map_mul, map_inv, hn]
    rfl
  have hy₁2 : y₁ * y₁ = 1 := by
    calc y₁ * y₁ = (n : G) * (y * y) * (n : G)⁻¹ := by rw [hy₁def]; group
      _ = 1 := by rw [hy2]; group
  let Θ : Subgroup G := (Rh.comap c.rho).map c.N1.subtype
  have hΘ : ∀ x : G, x ∈ Θ ↔ ∃ h : x ∈ c.N1, c.rho ⟨x, h⟩ ∈ Rh := by
    intro x
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, hm⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  have hRΘ : R ≤ Θ := by
    intro r hr
    rw [hΘ]
    exact ⟨hr.2, c.mem_Rhat.2 ⟨⟨r, hr.2⟩, hr, rfl⟩⟩
  have hΘN : Θ ≤ c.N1 := fun x hx => ((hΘ x).1 hx).1
  have hRodd : ¬ 2 ∣ R.relIndex Θ := by
    have h1 : R.relIndex Θ * Θ.relIndex c.N1 = R.relIndex c.N1 :=
      relIndex_mul_relIndex R Θ c.N1 hRΘ hΘN
    exact fun hd => hR.R_odd (dvd_trans hd (Dvd.intro _ h1))
  have hRmax : ∀ P' : Subgroup G, IsPGroup 2 P' → P' ≤ Θ → R ≤ P' → P' ≤ R :=
    max_of_odd_relIndex hR.R_pgroup hRodd
  have hy₁Θ : y₁ ∈ Θ := by
    rw [hΘ]
    refine ⟨hy₁N, ?_⟩
    rw [hρy₁]
    exact mem_subgroupOf.1 hgP
  have hz₁ : IsPGroup 2 (zpowers y₁) := by
    have hord : orderOf y₁ ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hy₁2)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨Q, ⟨hQ2, hQΘ, hyQ⟩, hQmax⟩ :=
    (Set.toFinite {Q : Subgroup G | IsPGroup 2 Q ∧ Q ≤ Θ ∧ zpowers y₁ ≤ Q}).exists_maximalFor
      id _ ⟨zpowers y₁, hz₁, zpowers_le.2 hy₁Θ, le_rfl⟩
  have hQmax' : ∀ Q' : Subgroup G, IsPGroup 2 Q' → Q' ≤ Θ → Q ≤ Q' → Q' ≤ Q :=
    fun Q' hQ' hQ'Θ hQQ' => hQmax ⟨hQ', hQ'Θ, hyQ.trans hQQ'⟩ hQQ'
  obtain ⟨w, hwΘ, hw⟩ := sylow_conj hRΘ hQΘ hR.R_pgroup hQ2 hRmax hQmax'
  obtain ⟨u, hudef⟩ : ∃ u : G, u = w⁻¹ := ⟨_, rfl⟩
  have huΘ : u ∈ Θ := by
    rw [hudef]
    exact inv_mem hwΘ
  have hy'eq : u * y₁ * u⁻¹ = w⁻¹ * y₁ * w := by
    rw [hudef, inv_inv]
  have hy'R : u * y₁ * u⁻¹ ∈ R := by
    rw [hy'eq]
    exact (hw _).1 (hyQ (mem_zpowers _))
  have hu1 : u ∈ c.N1 := ((hΘ u).1 huΘ).1
  have hu2 : c.rho ⟨u, hu1⟩ ∈ Rh := ((hΘ u).1 huΘ).2
  have hy'N : u * y₁ * u⁻¹ ∈ c.N1 := hy'R.2
  set W : MulAut ↥E × MulAut ↥E := c.rho ⟨u, hu1⟩ with hWdef
  have hρy' : c.rho ⟨u * y₁ * u⁻¹, hy'N⟩ = W * sg * W⁻¹ := by
    have e : (⟨u * y₁ * u⁻¹, hy'N⟩ : ↥c.N1) = ⟨u, hu1⟩ * ⟨y₁, hy₁N⟩ * ⟨u, hu1⟩⁻¹ :=
      Subtype.ext rfl
    rw [e, map_mul, map_mul, map_inv, hρy₁]
  have hcard : 2 ^ 9 ≤ Nat.card ↥(Rh ⊓
      centralizer ({c.rho ⟨u * y₁ * u⁻¹, hy'N⟩} : Set (MulAut ↥E × MulAut ↥E))) := by
    rw [hρy']
    have hmemI : ∀ x : ↥(P ⊓ centralizer ({g * ψ * g⁻¹} : Set ↥c.rho.range)),
        (x : ↥c.rho.range).1 ∈ Rh ⊓ centralizer ({sg} : Set (MulAut ↥E × MulAut ↥E)) := by
      intro x
      obtain ⟨hxP, hxc⟩ := Subgroup.mem_inf.1 x.2
      refine Subgroup.mem_inf.2 ⟨mem_subgroupOf.1 hxP, ?_⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have h1 := congrArg Subtype.val (mem_centralizer_singleton_iff.1 hxc)
      exact h1
    have hi : Nat.card ↥(P ⊓ centralizer ({g * ψ * g⁻¹} : Set ↥c.rho.range)) ≤
        Nat.card ↥(Rh ⊓ centralizer ({sg} : Set (MulAut ↥E × MulAut ↥E))) := by
      refine Nat.card_le_card_of_injective (fun x => ⟨(x : ↥c.rho.range).1, hmemI x⟩) ?_
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      have h1 := congrArg Subtype.val hab
      exact h1
    have hinj : Function.Injective (MulAut.conj W).toMonoidHom := (MulAut.conj W).injective
    have hsub : (Rh ⊓ centralizer ({sg} : Set (MulAut ↥E × MulAut ↥E))).map
        (MulAut.conj W).toMonoidHom ≤
          Rh ⊓ centralizer ({W * sg * W⁻¹} : Set (MulAut ↥E × MulAut ↥E)) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxR, hxc⟩ := Subgroup.mem_inf.1 hx
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hu2 hxR) (inv_mem hu2), ?_⟩
      refine mem_centralizer_singleton_iff.2 ?_
      have hxs : x * sg = sg * x := mem_centralizer_singleton_iff.1 hxc
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc W * x * W⁻¹ * (W * sg * W⁻¹) = W * (x * sg) * W⁻¹ := by group
        _ = W * (sg * x) * W⁻¹ := by rw [hxs]
        _ = W * sg * W⁻¹ * (W * x * W⁻¹) := by group
    have hii : Nat.card ↥(Rh ⊓ centralizer ({sg} : Set (MulAut ↥E × MulAut ↥E))) ≤
        Nat.card ↥(Rh ⊓ centralizer ({W * sg * W⁻¹} : Set (MulAut ↥E × MulAut ↥E))) := by
      have e1 := Subgroup.card_map_of_injective (f := (MulAut.conj W).toMonoidHom) hinj
        (K := Rh ⊓ centralizer ({sg} : Set (MulAut ↥E × MulAut ↥E)))
      rw [← e1]
      exact Subgroup.card_le_of_le hsub
    exact hgC.trans (hi.trans hii)
  refine ⟨u * y₁ * u⁻¹, hy'R, ⟨u * n, mul_mem hu1 n.2, ?_⟩, hcard⟩
  rw [hy₁def]
  group


theorem IsRs.not_conj_z_of_mem_R_pt {Rs : Subgroup G} (hR : c.IsRs Rs)
    (hT : Nat.card T ≤ 512) {y : G} (hy : y ∈ Rs ⊓ c.N1) (hy2 : y * y = 1)
    (hbig : 2 ^ 9 ∣ Nat.card ↥(Subgroup.centralizer
      ({(⟨c.rho ⟨y, hy.2⟩, ⟨⟨y, hy.2⟩, rfl⟩⟩ : ↥c.rho.range)} : Set ↥c.rho.range)))
    (hyz : ∃ g : G, y = g * z * g⁻¹) : False := by
  by_cases hyZ : y ∈ c.Zs
  · exact c.not_conj_z_of_mem_Zs hyZ hyz
  obtain ⟨y', hy', ⟨n, hn, hy'eq⟩, hcard⟩ := hR.exists_good_conj_pt hy hy2 hbig
  have hy'Z : y' ∉ c.Zs := by
    intro h'
    apply hyZ
    have h1 : n * y' = y' * n := c.Zs_comm_N1 h' hn
    have hyeq : y = y' := by
      calc y = n⁻¹ * (n * y * n⁻¹) * n := by group
        _ = n⁻¹ * y' * n := by rw [← hy'eq]
        _ = n⁻¹ * (y' * n) := by group
        _ = n⁻¹ * (n * y') := by rw [h1]
        _ = y' := by group
    rw [hyeq]
    exact h'
  have hy'z : ∃ g : G, y' = g * z * g⁻¹ := by
    obtain ⟨g, hg⟩ := hyz
    exact ⟨n * g, by rw [hy'eq, hg]; group⟩
  exact c.false_of_big_cent hR.R_pgroup inf_le_right hR.Zs_le_R hR.R_inf_KR_le hy' hy'Z hy'z
    hT hcard

end OI13Ctx

end CFSG.EvenSporadicStandard.Fin76b
