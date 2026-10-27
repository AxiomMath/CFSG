module

public import CFSG.GF2Type.Aschbacher1976Full.HSCruxBasic
public import CFSG.GF2Type.Aschbacher1976Full.HSPartCTwo

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS

open CFSG CFSG.Blueprint Subgroup PartC

variable {G : Type} [Group G] [Finite G]

@[expose] def cruxPIncl (z u : G) : ↥((Fz u ⊓ Hz z).subgroupOf (Hz z)) →* G :=
  (Hz z).subtype.comp ((Fz u ⊓ Hz z).subgroupOf (Hz z)).subtype

@[expose] def cruxPHom (z u : G) : ↥((Fz u ⊓ Hz z).subgroupOf (Hz z)) →* Qbar z :=
  (qmk z).comp ((Fz u ⊓ Hz z).subgroupOf (Hz z)).subtype

@[expose] def cruxPImage (z u : G) : Subgroup (Qbar z) := (cruxPHom z u).range

theorem mem_cruxPImage {z u : G} {x : Qbar z} :
    x ∈ cruxPImage z u ↔ ∃ g : ↥(Hz z), (g : G) ∈ Fz u ⊓ Hz z ∧ qmk z g = x := by
  rw [cruxPImage, MonoidHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1, Subgroup.mem_subgroupOf.mp y.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, Subgroup.mem_subgroupOf.mpr hg⟩, rfl⟩

theorem cruxPIncl_injective (z u : G) : Function.Injective (cruxPIncl z u) :=
  fun a b h => Subtype.ext (Subtype.ext h)

theorem cruxMapKer_le (z u : G) : ((cruxPHom z u).ker).map (cruxPIncl z u) ≤ Fz u ⊓ Fz z := by
  rintro _ ⟨p, hp, rfl⟩
  have h1 : qmk z (p : ↥(Hz z)) = 1 := MonoidHom.mem_ker.mp hp
  have h2 := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp p.2)
  exact Subgroup.mem_inf.mpr ⟨h2.1, (qmk_eq_one_iff z _).mp h1⟩

theorem cruxQmk_mul_eq {z : G} {a b : ↥(Hz z)}
    (h : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ Fz z) :
    qmk z a * qmk z b = qmk z b * qmk z a := by
  have h1 : qmk z (a * b * a⁻¹ * b⁻¹) = 1 := (qmk_eq_one_iff z (a * b * a⁻¹ * b⁻¹)).mpr h
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc qmk z a * qmk z b
      = (qmk z a * qmk z b * (qmk z a)⁻¹ * (qmk z b)⁻¹) * (qmk z b * qmk z a) := by group
    _ = qmk z b * qmk z a := by rw [h1, one_mul]

theorem cruxIsPGroup_closure {Q : Type*} [Group Q] {a : Q} (ha : orderOf a = 2) :
    IsPGroup 2 ↥(Subgroup.closure ({a} : Set Q)) := by
  have h : Nat.card ↥(Subgroup.closure ({a} : Set Q)) = 2 := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers, ha]
  exact IsPGroup.of_card (n := 1) (h.trans (pow_one 2).symm)

theorem cruxPImage_comm {z u : G} (huF : u ∈ Fz z)
    (hcomm : ∀ p ∈ Fz u ⊓ Hz z, ∀ p' ∈ Fz u ⊓ Hz z, p * p' * p⁻¹ * p'⁻¹ ∈ Subgroup.zpowers u)
    {x y : Qbar z} (hx : x ∈ cruxPImage z u) (hy : y ∈ cruxPImage z u) : x * y = y * x := by
  obtain ⟨g, hg, rfl⟩ := mem_cruxPImage.mp hx
  obtain ⟨g', hg', rfl⟩ := mem_cruxPImage.mp hy
  exact cruxQmk_mul_eq ((Subgroup.zpowers_le.mpr huF) (hcomm _ hg _ hg'))

theorem cruxPImage_sq {z u : G} (huF : u ∈ Fz z)
    (hsq : ∀ p ∈ Fz u ⊓ Hz z, p * p ∈ Subgroup.zpowers u) {x : Qbar z}
    (hx : x ∈ cruxPImage z u) : x * x = 1 := by
  obtain ⟨g, hg, rfl⟩ := mem_cruxPImage.mp hx
  rw [← map_mul, qmk_eq_one_iff]
  exact (Subgroup.zpowers_le.mpr huF) (hsq _ hg)

theorem cruxConj_mem {z u : G} (c : ↥(Hz z))
    (hc : ∀ p ∈ Fz u ⊓ Hz z, (c : G) * p * (c : G)⁻¹ ∈ Fz u ⊓ Hz z) {x : Qbar z}
    (hx : x ∈ cruxPImage z u) : qmk z c * x * (qmk z c)⁻¹ ∈ cruxPImage z u := by
  obtain ⟨g, hg, rfl⟩ := mem_cruxPImage.mp hx
  rw [mem_cruxPImage]
  refine ⟨c * g * c⁻¹, hc _ hg, ?_⟩
  simp only [map_mul, map_inv]

theorem cruxFour_le_card {z u : G} (hP : Nat.card ↥(Fz u ⊓ Hz z : Subgroup G) = 32)
    (hK : Nat.card ↥(Fz u ⊓ Fz z : Subgroup G) ≤ 8) : 4 ≤ Nat.card ↥(cruxPImage z u) := by
  have hS : Nat.card ↥((Fz u ⊓ Hz z).subgroupOf (Hz z)) = 32 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Fz u ⊓ Hz z ≤ Hz z)).toEquiv).trans hP
  have hdec := Subgroup.card_eq_card_quotient_mul_card_subgroup (cruxPHom z u).ker
  have hY : Nat.card ↥(cruxPImage z u) =
      Nat.card (↥((Fz u ⊓ Hz z).subgroupOf (Hz z)) ⧸ (cruxPHom z u).ker) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (cruxPHom z u)).toEquiv.symm
  have hK' : Nat.card ↥(cruxPHom z u).ker ≤ 8 := by
    calc Nat.card ↥(cruxPHom z u).ker
        = Nat.card ↥(((cruxPHom z u).ker).map (cruxPIncl z u)) :=
          (Subgroup.card_map_of_injective (K := (cruxPHom z u).ker) (cruxPIncl_injective z u)).symm
      _ ≤ Nat.card ↥(Fz u ⊓ Fz z : Subgroup G) := Subgroup.card_le_of_le (cruxMapKer_le z u)
      _ ≤ 8 := hK
  have h32 : Nat.card ↥(cruxPImage z u) * Nat.card ↥(cruxPHom z u).ker = 32 := by
    rw [hY, ← hdec, hS]
  by_contra hlt
  push_neg at hlt
  have h3 : Nat.card ↥(cruxPImage z u) ≤ 3 := by omega
  have hmul := Nat.mul_le_mul h3 hK'
  rw [h32] at hmul
  norm_num at hmul

theorem cruxConjMulZ {z u : G} (hzz : z * z = 1) (hFH : Fz z ≤ Hz z) {a : G} (haF : a ∈ Fz z)
    (ha : a⁻¹ * u * a = u * z) (h : ↥(Hz z)) (huh : (h : G) * u * (h : G)⁻¹ = u * z) :
    ∃ c : ↥(Hz z), (c : G) * u = u * (c : G) ∧ qmk z c = qmk z h := by
  have hcomm : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp (hFH haF)
  have hz1 : a⁻¹ * z = z * a⁻¹ := by
    calc a⁻¹ * z = a⁻¹ * (z * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * z) * a⁻¹ := by rw [hcomm]
      _ = z * a⁻¹ := by group
  have hza : a⁻¹ * z * a = z := by rw [hz1]; group
  have key : a⁻¹ * (u * z) * a = u := by
    calc a⁻¹ * (u * z) * a = (a⁻¹ * u * a) * (a⁻¹ * z * a) := by group
      _ = (u * z) * z := by rw [ha, hza]
      _ = u := by rw [mul_assoc, hzz, mul_one]
  have haF' : a⁻¹ ∈ Fz z := (Fz z).inv_mem haF
  obtain ⟨a', ha'⟩ : ∃ a' : ↥(Hz z), (a' : G) = a⁻¹ := ⟨⟨a⁻¹, hFH haF'⟩, rfl⟩
  have hqa : qmk z a' = 1 := (qmk_eq_one_iff z a').mpr (by rw [ha']; exact haF')
  refine ⟨a' * h, ?_, ?_⟩
  · have hc : ((a' * h : ↥(Hz z)) : G) = a⁻¹ * (h : G) := by rw [Subgroup.coe_mul, ha']
    rw [hc]
    calc a⁻¹ * (h : G) * u = a⁻¹ * ((h : G) * u * (h : G)⁻¹) * (h : G) := by group
      _ = a⁻¹ * (u * z) * (h : G) := by rw [huh]
      _ = (a⁻¹ * (u * z) * a) * (a⁻¹ * (h : G)) := by group
      _ = u * (a⁻¹ * (h : G)) := by rw [key]
  · rw [map_mul, hqa, one_mul]

theorem cruxDecomp {z : G} (hset : HSSetting G z) (hti : HSTI z) (hfib : FibreProp z)
    (htrans : ∀ d ∈ Dtil z, ∀ e ∈ Dtil z, ∃ m ∈ Subgroup.closure (Dtil z), m * d * m⁻¹ = e)
    {u : G} (hu : u ∈ Dinv z) (q : Qbar z) :
    ∃ m ∈ Subgroup.closure (Dtil z), ∃ c : ↥(Hz z), (c : G) * u = u * (c : G) ∧ q = m * qmk z c := by
  have hset' := hset
  obtain ⟨⟨_, _, hz, hsymp⟩, hZ4⟩ := hset'
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  obtain ⟨Z, A, hD⟩ := Width.exists_Z4Data hZ4
  have hFH : Fz z ≤ Hz z := Subgroup.map_subtype_le _
  have huF : u ∈ Fz z := (hti.2 u hu).1
  obtain ⟨-, -, -, hu2, hu1⟩ := ZF_props hD hz hF2 hu.1
  have hzz : z * z = 1 := by rw [← pow_two]; exact Width.z_sq hz
  have huu : u * u = 1 := by rw [← pow_two]; exact hu2
  have hyuD : yBar z u ∈ Dtil z := Set.mem_image_of_mem _ hu
  have hdq : q * yBar z u * q⁻¹ ∈ Dtil z := (dtil_hyps hset hti hfib).2.2.1 q _ hyuD
  obtain ⟨m, hm, hmq⟩ := htrans (yBar z u) hyuD _ hdq
  obtain ⟨h, hh⟩ := qmk_surjective z (m⁻¹ * q)
  have hfix : qmk z h * yBar z u * (qmk z h)⁻¹ = yBar z u := by
    rw [hh]
    calc m⁻¹ * q * yBar z u * (m⁻¹ * q)⁻¹ = m⁻¹ * (q * yBar z u * q⁻¹) * m := by group
      _ = m⁻¹ * (m * yBar z u * m⁻¹) * m := by rw [hmq]
      _ = yBar z u := by group
  have hu' : (h : G) * u * (h : G)⁻¹ ∈ Dinv z := Dinv_conj hu h.2
  have hyu' : yBar z ((h : G) * u * (h : G)⁻¹) = yBar z u := by
    rw [yBar_conj hD hz hF2 hti hu h, hfix]
  have hP2 : IsPGroup 2 ↥(Subgroup.closure
      ({yBar z u, yBar z ((h : G) * u * (h : G)⁻¹)} : Set (Qbar z))) := by
    rw [hyu', Set.pair_eq_singleton]
    exact cruxIsPGroup_closure (orderOf_yBar hD hz hF2 hti hu)
  rcases hfib u hu _ hu' hP2 with huu' | huu'
  · refine ⟨m, hm, h, ?_, by rw [hh]; group⟩
    calc (h : G) * u = ((h : G) * u * (h : G)⁻¹) * (h : G) := by group
      _ = u * (h : G) := by rw [huu']
  · obtain ⟨a, haF, ha⟩ := exists_conj_mul_z' hD hz huF hu1 hu.2.1 huu
    obtain ⟨c, hcu, hqc⟩ := cruxConjMulZ hzz hFH haF ha h huu'
    exact ⟨m, hm, c, hcu, by rw [hqc, hh]; group⟩

theorem cruxFrattini_holds : CruxFrattiniStmt := by
  intro G _ _ z hset hti hfib hPL htrans
  have hset' := hset
  obtain ⟨⟨_, _, _, hsymp⟩, _⟩ := hset'
  have hF2 : IsPGroup 2 ↥(Fz z) := hsymp.1
  have hconj := (dtil_hyps hset hti hfib).2.2.1
  obtain ⟨u, hu⟩ := hti.1
  have huF : u ∈ Fz z := (hti.2 u hu).1
  obtain ⟨-, hPcard, -, hKcard, hsqP, hcomP, hconjP⟩ := hPL u hu
  have hY4 := cruxFour_le_card hPcard hKcard
  obtain ⟨R, hR⟩ : ∃ R : Subgroup (Qbar z), R = cruxPImage z u ⊓ Subgroup.centralizer (Dtil z) :=
    ⟨_, rfl⟩
  have hRmem : ∀ r : Qbar z, r ∈ R ↔ r ∈ cruxPImage z u ∧ ∀ d ∈ Dtil z, d * r = r * d := by
    intro r
    rw [hR, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  have hRn : R.Normal := by
    refine ⟨fun r hr q => ?_⟩
    obtain ⟨hrY, hrC⟩ := (hRmem r).mp hr
    obtain ⟨m, hm, c, hcu, rfl⟩ := cruxDecomp hset hti hfib htrans hu q
    have hr'Y : qmk z c * r * (qmk z c)⁻¹ ∈ cruxPImage z u :=
      cruxConj_mem c (fun p hp => hconjP (c : G) c.2 hcu p hp) hrY
    have hr'C : ∀ d ∈ Dtil z, d * (qmk z c * r * (qmk z c)⁻¹) = (qmk z c * r * (qmk z c)⁻¹) * d := by
      intro d hd
      have hd' : (qmk z c)⁻¹ * d * qmk z c ∈ Dtil z := by
        have := hconj (qmk z c)⁻¹ d hd
        rwa [inv_inv] at this
      have h1 := hrC _ hd'
      calc d * (qmk z c * r * (qmk z c)⁻¹)
          = qmk z c * (((qmk z c)⁻¹ * d * qmk z c) * r) * (qmk z c)⁻¹ := by group
        _ = qmk z c * (r * ((qmk z c)⁻¹ * d * qmk z c)) * (qmk z c)⁻¹ := by rw [h1]
        _ = (qmk z c * r * (qmk z c)⁻¹) * d := by group
    have hr' : qmk z c * r * (qmk z c)⁻¹ ∈ R := (hRmem _).mpr ⟨hr'Y, hr'C⟩
    have hcl : Subgroup.closure (Dtil z) ≤ Subgroup.centralizer {qmk z c * r * (qmk z c)⁻¹} := by
      rw [Subgroup.closure_le]
      intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hr'C d hd)
    have hmc : m * (qmk z c * r * (qmk z c)⁻¹) = (qmk z c * r * (qmk z c)⁻¹) * m :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcl hm)
    have e : m * qmk z c * r * (m * qmk z c)⁻¹ = qmk z c * r * (qmk z c)⁻¹ := by
      calc m * qmk z c * r * (m * qmk z c)⁻¹ = m * (qmk z c * r * (qmk z c)⁻¹) * m⁻¹ := by group
        _ = (qmk z c * r * (qmk z c)⁻¹) * m * m⁻¹ := by rw [hmc]
        _ = qmk z c * r * (qmk z c)⁻¹ := by group
    rw [e]
    exact hr'
  have hR2 : IsPGroup 2 ↥R := by
    intro g
    refine ⟨1, ?_⟩
    have hg : (g : Qbar z) * (g : Qbar z) = 1 := cruxPImage_sq huF hsqP ((hRmem g.1).mp g.2).1
    show g ^ 2 = 1
    apply Subtype.ext
    simpa [pow_two] using hg
  have hRbot : R = ⊥ := O2_quotient_trivial hF2 R hRn hR2
  unfold HasYStmt
  refine ⟨cruxPImage z u, ?_, ?_, hY4, ?_⟩
  · intro x hx y hy
    exact cruxPImage_comm huF hcomP hx hy
  · intro x hx
    exact cruxPImage_sq huF hsqP hx
  · intro y hy hyd
    have hyR : y ∈ R := (hRmem y).mpr ⟨hy, fun d hd => (hyd d hd).symm⟩
    rw [hRbot] at hyR
    exact Subgroup.mem_bot.mp hyR

end CFSG.GF2Type.Aschbacher1976Full.HS
