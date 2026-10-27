module

public import CFSG.GH74.Generic.S45.PumpC1
public import CFSG.GH74.Generic.S45.PumpB1
public import CFSG.GH74.Generic.S45.PumpB2

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools Subgroup
open scoped Pointwise

section C2

variable {G : Type} [Group G] [Finite G] {x : G} {K : Subgroup (CentralizerBar x)} {T : Subgroup G}

theorem S45Conf.eq_of_proj_eq (h : S45Conf x K T) {v a b : G} (ha : a ∈ T) (hb : b ∈ T)
    (hav : a ∈ centralizer ({v} : Set G)) (hbv : b ∈ centralizer ({v} : Set G))
    (hab : proj v ⟨a, hav⟩ = proj v ⟨b, hbv⟩) : a = b := by
  have hinv : (a⁻¹ * b) ∈ centralizer ({v} : Set G) := mul_mem (inv_mem hav) hbv
  have h1 : proj v ⟨a⁻¹ * b, hinv⟩ = 1 := by
    have : (⟨a⁻¹ * b, hinv⟩ : ↥(centralizer ({v} : Set G))) = ⟨a, hav⟩⁻¹ * ⟨b, hbv⟩ := rfl
    rw [this, map_mul, map_inv, hab, inv_mul_cancel]
  have h2 : a⁻¹ * b = 1 :=
    eq_one_of_proj_eq_one_of_sq hinv h1 (h.sq _ (mul_mem (inv_mem ha) hb))
  exact inv_mul_eq_one.1 h2

theorem S45Conf.two_subgroup_elementary (h : S45Conf x K T) {v : G} (hvT : v ∈ T)
    (hxv : x ∈ centralizer ({v} : Set G)) (P : Subgroup (CentralizerBar v)) (hP : IsPGroup 2 ↥P)
    (hPc : P ≤ centralizer ({proj v ⟨x, hxv⟩} : Set (CentralizerBar v))) :
    (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) ∧ ∀ a ∈ P, a * a = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({v} : Set G) with hY
  have hYv : Y ≤ centralizer ({v} : Set G) := inf_le_right
  have hTY : T ≤ Y := by
    intro t ht
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.comm t ht x h.x_mem
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact h.comm t ht v hvT
  have hTsyl : IsSylowOf 2 T Y := h.sylow.of_le hTY inf_le_left
  let f : ↥Y →* CentralizerBar v := (proj v).comp (Subgroup.inclusion hYv)
  have hlift : ∀ p ∈ P, ∃ g : ↥Y, f g = p := by
    intro p hp
    have hpc : p * proj v ⟨x, hxv⟩ = proj v ⟨x, hxv⟩ * p :=
      Subgroup.mem_centralizer_singleton_iff.1 (hPc hp)
    obtain ⟨g, hg, hgp⟩ := proj_cent v (u := ⟨x, hxv⟩)
      (by apply Subtype.ext; exact h.sq x h.x_mem) p hpc
    have hgx : (g : G) ∈ centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hg
    exact ⟨⟨(g : G), Subgroup.mem_inf.2 ⟨hgx, g.2⟩⟩, hgp⟩
  let Pt : Subgroup ↥Y := P.comap f
  let f' : ↥Pt →* ↥P := (f.comp Pt.subtype).codRestrict P (fun g => g.2)
  have hf' : Function.Surjective f' := by
    rintro ⟨p, hp⟩
    obtain ⟨g, hg⟩ := hlift p hp
    exact ⟨⟨g, by show f g ∈ P; rw [hg]; exact hp⟩, Subtype.ext hg⟩
  obtain ⟨S₀⟩ : Nonempty (Sylow 2 ↥P) := inferInstance
  have hS₀ : (⊤ : Subgroup ↥P) = (S₀ : Subgroup ↥P) :=
    S₀.is_maximal' (hP.to_subgroup ⊤) le_top
  obtain ⟨T₀, hT₀⟩ := exists_sylow_map_eq f' hf' S₀
  let Q : Subgroup G := ((T₀ : Subgroup ↥Pt).map Pt.subtype).map Y.subtype
  have hQ2 : IsPGroup 2 ↥Q := (T₀.isPGroup'.map Pt.subtype).map Y.subtype
  have hQY : Q ≤ Y := by
    rintro _ ⟨_, _, rfl⟩
    exact (Subtype.property _)
  have hQlift : ∀ p ∈ P, ∃ (q : G) (hq : q ∈ Y), q ∈ Q ∧ f ⟨q, hq⟩ = p := by
    intro p hp
    have hmem : (⟨p, hp⟩ : ↥P) ∈ (T₀ : Subgroup ↥Pt).map f' := by rw [hT₀, ← hS₀]; trivial
    obtain ⟨t, ht, hft⟩ := hmem
    refine ⟨((t : ↥Pt) : ↥Y), ((t : ↥Pt) : ↥Y).2, ⟨(t : ↥Y), ⟨t, ht, rfl⟩, rfl⟩, ?_⟩
    have := congrArg Subtype.val hft
    exact this
  have hQ' : IsPGroup 2 ↥(Q.subgroupOf Y) := hQ2.comap_subtype
  obtain ⟨S', hS'⟩ := hQ'.exists_le_sylow
  have hS'' : IsSylowOf 2 ((S' : Subgroup ↥Y).map Y.subtype) Y := ⟨S', rfl⟩
  obtain ⟨k, hkY, hk⟩ := hTsyl.exists_mem_conj hS''
  have hQS : ∀ a ∈ Q, a ∈ (S' : Subgroup ↥Y).map Y.subtype :=
    fun a ha => ⟨⟨a, hQY ha⟩, hS' ha, rfl⟩
  have hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
    intro a ha b hb
    have hka := (hk a).1 (hQS a ha)
    have hkb := (hk b).1 (hQS b hb)
    have h1 := h.comm _ hka _ hkb
    have h2 : k⁻¹ * (a * b) * k = k⁻¹ * (b * a) * k := by
      calc k⁻¹ * (a * b) * k = k⁻¹ * a * k * (k⁻¹ * b * k) := by group
        _ = k⁻¹ * b * k * (k⁻¹ * a * k) := h1
        _ = k⁻¹ * (b * a) * k := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hQsq : ∀ a ∈ Q, a * a = 1 := by
    intro a ha
    have hka := (hk a).1 (hQS a ha)
    have h1 := h.sq _ hka
    have h2 : k⁻¹ * (a * a) * k = k⁻¹ * 1 * k := by
      calc k⁻¹ * (a * a) * k = k⁻¹ * a * k * (k⁻¹ * a * k) := by group
        _ = 1 := h1
        _ = k⁻¹ * 1 * k := by group
    exact mul_left_cancel (mul_right_cancel h2)
  refine ⟨fun p hp p' hp' => ?_, fun p hp => ?_⟩
  · obtain ⟨q, hq, hqQ, hqp⟩ := hQlift p hp
    obtain ⟨q', hq', hq'Q, hq'p⟩ := hQlift p' hp'
    rw [← hqp, ← hq'p, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hQcomm q hqQ q' hq'Q
  · obtain ⟨q, hq, hqQ, hqp⟩ := hQlift p hp
    rw [← hqp, ← map_mul]
    have : (⟨q, hq⟩ * ⟨q, hq⟩ : ↥Y) = 1 := Subtype.ext (hQsq q hqQ)
    rw [this, map_one]

omit [Finite G] in
theorem card_centralizer_conj (x g : G) :
    Nat.card ↥(centralizer ({g * x * g⁻¹} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
  apply Nat.card_congr
  refine ⟨fun a => ⟨g⁻¹ * (a : G) * g, ?_⟩, fun b => ⟨g * (b : G) * g⁻¹, ?_⟩, ?_, ?_⟩
  · have ha := Subgroup.mem_centralizer_singleton_iff.1 a.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g⁻¹ * (a : G) * g * x = g⁻¹ * ((a : G) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (a : G)) * g := by rw [ha]
      _ = x * (g⁻¹ * (a : G) * g) := by group
  · have hb := Subgroup.mem_centralizer_singleton_iff.1 b.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * (b : G) * g⁻¹ * (g * x * g⁻¹) = g * ((b : G) * x) * g⁻¹ := by group
      _ = g * (x * (b : G)) * g⁻¹ := by rw [hb]
      _ = (g * x * g⁻¹) * (g * (b : G) * g⁻¹) := by group
  · intro a
    apply Subtype.ext
    show g * (g⁻¹ * (a : G) * g) * g⁻¹ = a
    group
  · intro b
    apply Subtype.ext
    show g⁻¹ * (g * (b : G) * g⁻¹) * g = b
    group

theorem S45Conf.exists_two_central (h : S45Conf x K T) {v : G} (hvT : v ∈ T) (hvK : v ∈ Pre x K)
    (hv1 : v ≠ 1) : ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ v ∈ S ∧ ∀ s ∈ S, s * v = v * s := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hTQ⟩ := h.sylow.isPGroup.exists_le_sylow
  have hS₀syl : IsSylowOf 2 (Q : Subgroup G) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact Q.not_dvd_index
  have hTne : T ≠ (Q : Subgroup G) := fun hTS => h.not_sylow (hTS ▸ hS₀syl)
  have hxnot : x ∉ Pre x K := (h.fusion x h.x_mem).1 ⟨1, by simp⟩
  have hx1 : x ≠ 1 := fun h1 => hxnot (h1 ▸ one_mem (Pre x K))
  have hnt : Nontrivial ↥(Q : Subgroup G) := ⟨⟨⟨x, hTQ h.x_mem⟩, 1, fun h1 => hx1 (congrArg Subtype.val h1)⟩⟩
  have hcn : Nontrivial ↥(Subgroup.center ↥(Q : Subgroup G)) := Q.isPGroup'.center_nontrivial
  have hZ2 : 2 ∣ Nat.card ↥(Subgroup.center ↥(Q : Subgroup G)) := by
    have hZp : IsPGroup 2 ↥(Subgroup.center ↥(Q : Subgroup G)) := Q.isPGroup'.to_subgroup _
    obtain ⟨m, hm⟩ := hZp.exists_card_eq
    rcases m with _ | m
    · exfalso
      rw [pow_zero] at hm
      have := Nat.card_eq_one_iff_unique.1 hm
      obtain ⟨a, b, hab⟩ := hcn.1
      exact hab (this.1.elim a b)
    · rw [hm]
      exact dvd_pow_self 2 (Nat.succ_ne_zero m)
  obtain ⟨zz, hzz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥(Q : Subgroup G))) 2 hZ2
  set z : G := ((zz : ↥(Q : Subgroup G)) : G) with hz
  have hzQ : z ∈ (Q : Subgroup G) := (zz : ↥(Q : Subgroup G)).2
  have hzc : ∀ s ∈ (Q : Subgroup G), s * z = z * s := by
    intro s hs
    have := Subgroup.mem_center_iff.1 zz.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  have hz2 : z * z = 1 := by
    have h1 : orderOf (zz : ↥(Subgroup.center ↥(Q : Subgroup G))) = 2 := hzz
    have h2 : (zz : ↥(Subgroup.center ↥(Q : Subgroup G))) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (zz : ↥(Subgroup.center ↥(Q : Subgroup G)))
      rwa [h1] at this
    have h3 := congrArg (fun a : ↥(Subgroup.center ↥(Q : Subgroup G)) => ((a : ↥(Q : Subgroup G)) : G)) h2
    simpa [pow_two] using h3
  have hz1 : z ≠ 1 := by
    intro h1
    have : (zz : ↥(Subgroup.center ↥(Q : Subgroup G))) = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    rw [this, orderOf_one] at hzz
    omega
  have hzC : z ∈ centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hzc x (hTQ h.x_mem)).symm
  have hzT : z ∈ T := by
    set U : Subgroup G := T ⊔ zpowers z with hU
    have hUQ : U ≤ (Q : Subgroup G) := sup_le hTQ ((zpowers_le).2 hzQ)
    have hUC : U ≤ centralizer ({x} : Set G) :=
      sup_le h.sylow.le ((zpowers_le).2 hzC)
    have hU2 : IsPGroup 2 ↥U := Q.isPGroup'.to_le hUQ
    have := h.sylow.eq_of_le le_sup_left hUC hU2
    rw [← this]
    exact Subgroup.mem_sup_right (mem_zpowers z)
  have hzR : z ∈ Pre x K := by
    by_contra hzn
    obtain ⟨g, hg⟩ := (h.fusion z hzT).2 hzn
    have hcard1 : Nat.card ↥(centralizer ({z} : Set G)) = Nat.card ↥(centralizer ({x} : Set G)) := by
      rw [← hg]
      exact card_centralizer_conj x g
    have hQC : (Q : Subgroup G) ≤ centralizer ({z} : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hzc s hs
    have hdvd : Nat.card ↥(Q : Subgroup G) ∣ Nat.card ↥(centralizer ({x} : Set G)) := by
      rw [← hcard1]
      exact Subgroup.card_dvd_of_le hQC
    obtain ⟨m, hm⟩ := Q.isPGroup'.exists_card_eq
    have hcx : Nat.card ↥T = 2 ^ (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 :=
      h.sylow.card_eq
    have hmle : m ≤ (Nat.card ↥(centralizer ({x} : Set G))).factorization 2 := by
      rw [hm] at hdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
    have hcardle : Nat.card ↥(Q : Subgroup G) ≤ Nat.card ↥T := by
      rw [hm, hcx]
      exact Nat.pow_le_pow_right (by norm_num) hmle
    exact hTne (Subgroup.eq_of_le_of_card_ge hTQ hcardle)
  have hz1' : (⟨z, hzT⟩ : ↥T) ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  have hv1' : (⟨v, hvT⟩ : ↥T) ≠ 1 := fun h1 => hv1 (congrArg Subtype.val h1)
  obtain ⟨f, hf, hfz⟩ := h.exists_autGx_apply_eq (r := ⟨z, hzT⟩) (s := ⟨v, hvT⟩) hzR hvK hz1' hv1'
  obtain ⟨⟨n, hn⟩, rfl⟩ := hf.1
  have hnv : n * z * n⁻¹ = v := congrArg Subtype.val hfz
  refine ⟨((n • Q : Sylow 2 G) : Subgroup G), ?_, ?_, ?_⟩
  · rw [isSylowOf_iff]
    refine ⟨le_top, (n • Q).isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact (n • Q).not_dvd_index
  · have h1 : ((n • Q : Sylow 2 G) : Subgroup G) = MulAut.conj n • (Q : Subgroup G) :=
      Sylow.coe_subgroup_smul
    rw [h1, Subgroup.mem_smul_pointwise_iff_exists]
    exact ⟨z, hzQ, by simpa [MulAut.smul_def, MulAut.conj_apply] using hnv⟩
  · intro s hs
    have h1 : ((n • Q : Sylow 2 G) : Subgroup G) = MulAut.conj n • (Q : Subgroup G) :=
      Sylow.coe_subgroup_smul
    rw [h1, Subgroup.mem_smul_pointwise_iff_exists] at hs
    obtain ⟨q, hq, rfl⟩ := hs
    rw [← hnv]
    simp only [MulAut.smul_def, MulAut.conj_apply]
    have := hzc q hq
    calc n * q * n⁻¹ * (n * z * n⁻¹) = n * (q * z) * n⁻¹ := by group
      _ = n * (z * q) * n⁻¹ := by rw [this]
      _ = n * z * n⁻¹ * (n * q * n⁻¹) := by group

theorem S45Conf.controls_fusion (h : S45Conf x K T) {v : G} (hvT : v ∈ T) (hvK : v ∈ Pre x K)
    (hv1 : v ≠ 1) :
    ∀ g : G, g * v * g⁻¹ ∈ T → ∃ c ∈ centralizer ({x} : Set G), c * v * c⁻¹ = g * v * g⁻¹ := by
  intro g hgT
  set u : G := g * v * g⁻¹ with hu
  have hu1 : u ≠ 1 := by
    intro h1
    apply hv1
    have : v = g⁻¹ * u * g := by rw [hu]; group
    rw [this, h1]
    group
  have huR : u ∈ Pre x K := by
    by_contra hun
    obtain ⟨g', hg'⟩ := (h.fusion u hgT).2 hun
    refine ((h.fusion v hvT).1 ⟨g⁻¹ * g', ?_⟩) hvK
    calc g⁻¹ * g' * x * (g⁻¹ * g')⁻¹ = g⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g⁻¹ * u * g := by rw [hg']
      _ = v := by rw [hu]; group
  have hu1' : (⟨u, hgT⟩ : ↥T) ≠ 1 := fun h1 => hu1 (congrArg Subtype.val h1)
  have hv1' : (⟨v, hvT⟩ : ↥T) ≠ 1 := fun h1 => hv1 (congrArg Subtype.val h1)
  obtain ⟨f, hf, hfv⟩ := h.exists_autGx_apply_eq (r := ⟨v, hvT⟩) (s := ⟨u, hgT⟩) hvK huR hv1' hu1'
  obtain ⟨⟨n, hn⟩, rfl⟩ := hf.1
  have hnx : n * x * n⁻¹ = x := congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hf.2)
  refine ⟨n, ?_, congrArg Subtype.val hfv⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [mul_inv_eq_iff_eq_mul] at hnx
  exact hnx

omit [Finite G] in
theorem isSylowOf_top_of_le_centralizer [Finite G] {v : G} {S T' : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hSC : S ≤ centralizer ({v} : Set G)) (hT' : IsSylowOf 2 T' (centralizer ({v} : Set G))) :
    IsSylowOf 2 T' ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSc : Nat.card ↥S = 2 ^ (Nat.card ↥(⊤ : Subgroup G)).factorization 2 := hS.card_eq
  have hTc : Nat.card ↥T' = 2 ^ (Nat.card ↥(centralizer ({v} : Set G))).factorization 2 :=
    hT'.card_eq
  have hdvd : Nat.card ↥S ∣ Nat.card ↥(centralizer ({v} : Set G)) :=
    Subgroup.card_dvd_of_le hSC
  have hle : (Nat.card ↥(⊤ : Subgroup G)).factorization 2 ≤
      (Nat.card ↥(centralizer ({v} : Set G))).factorization 2 := by
    rw [hSc] at hdvd
    exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').1 hdvd
  have hle' : (Nat.card ↥(centralizer ({v} : Set G))).factorization 2 ≤
      (Nat.card ↥(⊤ : Subgroup G)).factorization 2 := by
    have hd : Nat.card ↥(centralizer ({v} : Set G)) ∣ Nat.card ↥(⊤ : Subgroup G) :=
      Subgroup.card_dvd_of_le le_top
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hd 2
  exact isSylowOf_of_card le_top (by rw [hTc, le_antisymm hle' hle])

theorem not_isJ1OrRee_of_central (hK : B_S45_KFacts) (hs : IsSimpleGroup G)
    (hn : ∃ a b : G, a * b ≠ b * a) (hgen : Gen4 G) {v : G} (hv : orderOf v = 2)
    (hcent : ∃ S : Subgroup G, IsSylowOf 2 S ⊤ ∧ v ∈ S ∧ ∀ s ∈ S, s * v = v * s)
    {J : Subgroup (CentralizerBar v)} (hJ : IsComponent J) (hj : IsJ1OrRee ↥J) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKB := hK ↥J hj
  have hnab := exists_noncomm_of_isQuasisimple hJ.1
  have hnot : xbar v ∉ J := by
    intro hmem
    have : (⟨xbar v, hmem⟩ : ↥J) = 1 := by
      apply eq_one_of_central_of_simple hKB.1 hnab
      intro w
      exact Subtype.ext (xbar_comm v w)
    exact xbar_ne_one hv (congrArg Subtype.val this)
  have hd : KData (CentralizerBar v) J (xbar v) :=
    { gen4 := gen4_centralizerBar hgen v
      oddcore := pPrimeCore_quotient_pPrimeCore_eq_bot _ 2
      central := fun g => xbar_comm v g
      sq := xbar_mul_self hv
      ne := xbar_ne_one hv
      comp := hJ
      notin := hnot
      facts := hKB }
  obtain ⟨R₀, T', hR₀K, hc⟩ := hd.exists_conf2 (card_D_eq_two hs hn hv hd)
  have hcard : Nat.card ↥T' = 16 := hc.lift.card_eq.trans hc.S_card
  have h315' : ∀ A' : Subgroup (MulAut ↥T'), Nat.card ↥A' ≠ 315 :=
    fun A' => no_subgroup_card_315 ↥T' hcard A'
  have hns := hc.not_isSylowOf_top hs hn hv h315'
  obtain ⟨S, hS, hvS, hSc⟩ := hcent
  have hSC : S ≤ centralizer ({v} : Set G) := fun s hs' => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hSc s hs'
  exact hns (isSylowOf_top_of_le_centralizer hS hSC hc.lift.sylow)

theorem S45Conf.not_barSub_le_centralizer (h : S45Conf x K T) {v : G} (hvT : v ∈ T)
    (hvK : v ∈ Pre x K) (hv1 : v ≠ 1) (hxv : x ∈ centralizer ({v} : Set G)) {W J : Subgroup G}
    (hWJ : W ≤ J) (hJH : J ≤ centralizer ({v} : Set G)) (hJsub : (barSub v J).IsSubnormal)
    {c : G} (hcW : c ∈ W) (hcN : c ∈ normalizer (T : Set G))
    (hc1 : T.normalizerMonoidHom ⟨c, hcN⟩ ≠ 1) :
    ¬ barSub v J ≤ centralizer ({proj v ⟨x, hxv⟩} : Set (CentralizerBar v)) := by
  intro hle
  set H : Subgroup G := centralizer ({v} : Set G) with hH
  let M : Subgroup G := ((barSub v J).comap (proj v)).map H.subtype
  have hMH : M ≤ H := Subgroup.map_subtype_le _
  have hMsub : (M.subgroupOf H).IsSubnormal := by
    have h1 : M.subgroupOf H = (barSub v J).comap (proj v) := by
      show Subgroup.comap H.subtype (Subgroup.map H.subtype _) = _
      exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [h1]
    exact hJsub.comap (proj v)
  have hcH : c ∈ H := hJH (hWJ hcW)
  have hcM : c ∈ M := ⟨⟨c, hcH⟩, proj_mem_barSub hcH (hWJ hcW), rfl⟩
  refine h.false_of_subnormal_pre (v := ⟨v, hvT⟩) hvK (fun h1 => hv1 (congrArg Subtype.val h1)) M hMH
    hMsub c hcM hcN hc1 ?_
  intro n hn hnN
  obtain ⟨u, hu, rfl⟩ := hn
  have hπ : proj v u ∈ barSub v J := hu
  have hcomm : proj v u * proj v ⟨x, hxv⟩ = proj v ⟨x, hxv⟩ * proj v u :=
    Subgroup.mem_centralizer_singleton_iff.1 (hle hπ)
  have hconjT : (u : G) * x * (u : G)⁻¹ ∈ T := conj_mem_T hnN h.x_mem
  have hconjH : (u : G) * x * (u : G)⁻¹ ∈ H := mul_mem (mul_mem u.2 hxv) (inv_mem u.2)
  have himg : proj v ⟨(u : G) * x * (u : G)⁻¹, hconjH⟩ = proj v ⟨x, hxv⟩ := by
    have : (⟨(u : G) * x * (u : G)⁻¹, hconjH⟩ : ↥H) = u * ⟨x, hxv⟩ * u⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
    exact mul_inv_eq_iff_eq_mul.2 hcomm
  exact h.eq_of_proj_eq hconjT h.x_mem hconjH hxv himg

end C2

end CFSG.GH74.Generic.S45
