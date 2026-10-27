module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13Cl1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8I13E8
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8SylExt

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OI13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B S : Subgroup G} {α σ : G}
  (c : OI13Ctx L z t T E B β S α σ)

include c

theorem Zs_le_S : c.Zs ≤ S := by
  intro u hu
  rcases c.mem_Zs.1 hu with h | h | h | h
  · rw [h]; exact S.one_mem
  · rw [h]; exact c.h.t_mem_S
  · rw [h]; exact c.hα.mem
  · rw [h]; exact mul_mem c.hα.mem c.h.t_mem_S

theorem z_not_mem_Zs : z ∉ c.Zs := by
  intro hz
  rcases c.mem_Zs.1 hz with h | h | h | h
  · exact c.h.z_ne h
  · exact c.h.z_ne_t h
  · exact c.hα.ne_z h.symm
  · apply c.hα.ne_zt
    calc α = α * (t * t) := by rw [c.h.t_sq, mul_one]
      _ = (α * t) * t := by group
      _ = z * t := by rw [← h]

theorem zt_not_mem_Zs : z * t ∉ c.Zs := by
  intro hz
  rcases c.mem_Zs.1 hz with h | h | h | h
  · apply c.h.z_ne_t
    have h1 : z * t = t * t := by rw [h, c.h.t_sq]
    exact mul_right_cancel h1
  · apply c.h.z_ne
    have h1 : z * t = 1 * t := by rw [h, one_mul]
    exact mul_right_cancel h1
  · exact c.hα.ne_zt h.symm
  · exact c.hα.ne_z (mul_right_cancel h).symm

theorem not_conj_z_of_mem_Zs {y : G} (hy : y ∈ c.Zs) (hyz : ∃ g : G, y = g * z * g⁻¹) :
    False := by
  obtain ⟨g, hg⟩ := hyz
  rw [hg] at hy
  rcases c.h.h67 g (c.Zs_le_S hy) with h | h
  · rw [h] at hy
    exact c.z_not_mem_Zs hy
  · rw [h] at hy
    exact c.zt_not_mem_Zs hy

variable {c}

theorem IsRs.exists_good_conj {Rs : Subgroup G} (hR : c.IsRs Rs)
    (hbig : ∀ ψ : ↥c.rho.range, ψ * ψ = 1 →
      2 ^ 9 ∣ Nat.card ↥(Subgroup.centralizer ({ψ} : Set ↥c.rho.range)))
    {y : G} (hy : y ∈ Rs ⊓ c.N1) (hy2 : y * y = 1) :
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
  obtain ⟨g, hgP, hgC⟩ := exists_conj_mem_sylow_big_cent hP hPmax hψ (hbig ψ hψ)
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

variable (c)

theorem false_of_big_cent {R : Subgroup G} (hR2 : IsPGroup 2 R) (hRN : R ≤ c.N1)
    (hZR : c.Zs ≤ R) (hKR : R ⊓ c.KR ≤ c.Zs) {y : G} (hy : y ∈ R) (hyZ : y ∉ c.Zs)
    (hyz : ∃ g : G, y = g * z * g⁻¹) (hT : Nat.card T ≤ 512)
    (hbig : 2 ^ 9 ≤ Nat.card ↥(c.Rhat R ⊓
      centralizer ({c.rho ⟨y, hRN hy⟩} : Set (MulAut ↥E × MulAut ↥E)))) : False := by
  have hcl := c.card_cent_Rhat_le hRN hZR hKR hy
  have h512 : (2 : ℕ) ^ 9 = 512 := by norm_num
  rw [h512] at hbig
  have hcent : 512 ≤ Nat.card ↥(R ⊓ centralizer ({y} : Set G)) := le_trans hbig hcl
  set C : Subgroup G := R ⊓ centralizer ({y} : Set G) with hC
  have hC2 : IsPGroup 2 C := hR2.to_le inf_le_left
  have hCy : C ≤ centralizer ({y} : Set G) := inf_le_right
  have hcard : Nat.card T ≤ Nat.card C := by omega
  have hbound := c.center_card_le hyz hC2 hCy hcard
  have hyC : y ∈ C := ⟨hy, mem_centralizer_singleton_iff.2 rfl⟩
  have hZmem : ∀ a ∈ c.Zs, a ∈ C := fun a ha =>
    ⟨hZR ha, mem_centralizer_singleton_iff.2 (c.Zs_comm_N1 ha (hRN hy)).symm⟩
  set Cs : Set G := {a : G | a ∈ C ∧ ∀ u ∈ C, a * u = u * a} with hCs
  have hCs_Zs : ∀ a ∈ c.Zs, a ∈ Cs := fun a ha =>
    ⟨hZmem a ha, fun u hu => (c.Zs_comm_N1 ha (hRN hu.1)).symm⟩
  have hCs_yZ : ∀ a ∈ c.Zs, y * a ∈ Cs := by
    intro a ha
    refine ⟨mul_mem hyC (hZmem a ha), fun u hu => ?_⟩
    have hu1 : u * y = y * u := mem_centralizer_singleton_iff.1 hu.2
    have hu2 : u * a = a * u := c.Zs_comm_N1 ha (hRN hu.1)
    calc y * a * u = y * (a * u) := by group
      _ = y * (u * a) := by rw [hu2]
      _ = (y * u) * a := by group
      _ = (u * y) * a := by rw [hu1]
      _ = u * (y * a) := by group
  have hsub : (c.Zs : Set G) ∪ (fun a => y * a) '' (c.Zs : Set G) ⊆ Cs := by
    rintro _ (ha | ⟨a, ha, rfl⟩)
    · exact hCs_Zs _ ha
    · exact hCs_yZ _ ha
  have hdisj : Disjoint (c.Zs : Set G) ((fun a => y * a) '' (c.Zs : Set G)) := by
    rw [Set.disjoint_left]
    rintro _ ha ⟨b, hb, rfl⟩
    apply hyZ
    have e : y = (y * b) * b⁻¹ := by group
    rw [e]
    exact mul_mem ha (inv_mem hb)
  have h8 : Set.ncard ((c.Zs : Set G) ∪ (fun a => y * a) '' (c.Zs : Set G)) = 8 := by
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injective _ (mul_right_injective y)]
    have h4 : Set.ncard (c.Zs : Set G) = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact c.card_Zs'
    omega
  have h9 := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

variable {c}

theorem IsRs.not_conj_z_of_mem_R {Rs : Subgroup G} (hR : c.IsRs Rs)
    (hbig : ∀ ψ : ↥c.rho.range, ψ * ψ = 1 →
      2 ^ 9 ∣ Nat.card ↥(Subgroup.centralizer ({ψ} : Set ↥c.rho.range)))
    (hT : Nat.card T ≤ 512) {y : G} (hy : y ∈ Rs ⊓ c.N1) (hy2 : y * y = 1)
    (hyz : ∃ g : G, y = g * z * g⁻¹) : False := by
  by_cases hyZ : y ∈ c.Zs
  · exact c.not_conj_z_of_mem_Zs hyZ hyz
  obtain ⟨y', hy', ⟨n, hn, hy'eq⟩, hcard⟩ := hR.exists_good_conj hbig hy hy2
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
