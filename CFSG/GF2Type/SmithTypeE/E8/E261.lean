module

public import CFSG.GF2Type.SmithTypeE.E8.E261Mod
public import CFSG.GF2Type.SmithTypeE.E8.E23a
public import CFSG.GF2Type.SmithTypeE.E8.IdentSimple

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open CFSG.LargeExtraspecial
  CFSG.LargeExtraspecial.S14
open CFSG.LieType.Steinberg.Minuscule (e7Data)
open CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors (e7Rep56 e7Y56 e7n6)
open CFSG.SeitzReduction (highRoot)
open CFSG.SeitzReduction.EPilot (pinnedElt perpLevi perpRoots pinnedElt_mem_perpLevi)
open CFSG.GF2Type.SmithTypeE.L6Ident (conj_inv_mem_M_of_commute)
open CFSG.LargeExtraspecial.S14.SME (mem_Qa_iff mem_Qa_symm)


variable {G : Type} [Group G] [Finite G]

theorem commute_conj_inv_E8 (g : G) {x y : G} (h : Commute x y) :
    Commute (g⁻¹ * x * g) (g⁻¹ * y * g) := by
  simpa using (commute_conj_iff_E8 g⁻¹ x y).2 h

theorem exists_conj_eq_mul_of_mem_Qa (hE : SmithE8E23a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1) {t u h a : G}
    (ht : IsConj S.z t) (hu : IsConj S.z u) (htu : orderOf (t * u) = 3)
    (hbt : Commute (h * S.z * h⁻¹) t) (hbu : Commute (h * S.z * h⁻¹) u) (ha : IsConj S.z a)
    (haQ : h⁻¹ * a * h ∈ S.QG) (hab : a ≠ h * S.z * h⁻¹) (hat : Commute a t)
    (hau : Commute a u) :
    ∃ q : G, Commute q t ∧ Commute q u ∧ q * (h * S.z * h⁻¹) * q⁻¹ = h * S.z * h⁻¹ * a := by
  have ht' : IsConj S.z (h⁻¹ * t * h) := ht.trans (isConj_iff.mpr ⟨h⁻¹, by group⟩)
  have hu' : IsConj S.z (h⁻¹ * u * h) := hu.trans (isConj_iff.mpr ⟨h⁻¹, by group⟩)
  have ha' : IsConj S.z (h⁻¹ * a * h) := ha.trans (isConj_iff.mpr ⟨h⁻¹, by group⟩)
  have htu' : orderOf ((h⁻¹ * t * h) * (h⁻¹ * u * h)) = 3 := by
    rw [show (h⁻¹ * t * h) * (h⁻¹ * u * h) = MulAut.conj h⁻¹ (t * u) by
      simp [MulAut.conj_apply]; group, MulEquiv.orderOf_eq]
    exact htu
  have haz : h⁻¹ * a * h ≠ S.z := fun e => hab (by
    calc a = h * (h⁻¹ * a * h) * h⁻¹ := by group
      _ = h * S.z * h⁻¹ := by rw [e])
  obtain ⟨q, hqt, hqu, hq⟩ := exists_conj_eq_z_mul hE S hw hU ht' hu'
    (conj_inv_mem_M_of_commute S hbt) (conj_inv_mem_M_of_commute S hbu) htu' ha' haQ haz
    (commute_conj_inv_E8 h hat) (commute_conj_inv_E8 h hau)
  refine ⟨h * q * h⁻¹, ?_, ?_, ?_⟩
  · have := commute_conj_inv_E8 h⁻¹ hqt
    simp only [inv_inv] at this
    rwa [show h * (h⁻¹ * t * h) * h⁻¹ = t by group] at this
  · have := commute_conj_inv_E8 h⁻¹ hqu
    simp only [inv_inv] at this
    rwa [show h * (h⁻¹ * u * h) * h⁻¹ = u by group] at this
  · calc h * q * h⁻¹ * (h * S.z * h⁻¹) * (h * q * h⁻¹)⁻¹ = h * (q * S.z * q⁻¹) * h⁻¹ := by group
      _ = h * (S.z * (h⁻¹ * a * h)) * h⁻¹ := by rw [hq]
      _ = h * S.z * h⁻¹ * a := by group

theorem mem_K_of_lift (hF : E23FourFacts8) (h33 : SmithE8E33) (h34a : SmithE8E34a)
    (h34b : SmithE8E34b) (hE : SmithE8E23a) [IsSimpleGroup G] (S : Setting G)
    (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}
    {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))} (hE0 : SmithE8Equiv S φ ψ)
    (h2a : ∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → φ (S.cl c) ∈ weightVec)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) (htu : orderOf (t * u) = 3)
    (hAt : Acts S φ t xT) (hAu : Acts S φ u xTn)
    {K : Subgroup G} (hQK : S.QG ⊓ cent2 t u ≤ K)
    (hnK : ∀ h ∈ cent2 t u, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    {y : G} (hyD : IsConj S.z y) (hyM : y ∈ S.M) (hyQ : y ∉ S.QG) (hyt : Commute y t)
    (hyu : Commute y u) {r : ↥(adjointGroup .E7 (ZMod 2))} (hr : IsRootInvol r)
    (hAy : Acts S φ y r) {w : Fin e7Data.d →₀ ZMod 2} (hwW : w ∈ weightVec)
    (hEw : InComm r w) (hwV : w ∈ V0) : y ∈ K := by
  obtain ⟨hwt, hwu⟩ := (mem_V0_iff w).1 hwV
  obtain ⟨g, hg⟩ := isConj_iff.mp hyD
  subst hg
  obtain ⟨b, hbD, hbQ, hbw, hbQa⟩ := exists_mem_Qa_of_class hF h33 h34a h34b S hw hU h2a
    (exists_acts_of_equiv hE0) hyM hyQ hr hAy hwW hEw
  have hcomm_b : ∀ {c : G} (hc : IsConj S.z c) (hcM : c ∈ S.M) (hcQ : c ∉ S.QG)
      {T : ↥(adjointGroup .E7 (ZMod 2))}, Acts S φ c T → e7Rep56 (ZMod 2) T w = w →
        Commute b c := by
    intro c hc hcM hcQ T hAc hTw
    have hcl : S.cl (c * b * c⁻¹) = S.cl b := by
      apply φ.injective
      rw [hAc b hbQ, hbw, hTw]
    have hfix := (S.cl_mem_fixQt_iff hcM hbQ).mpr hcl
    exact (S.commute_of_cl_mem_fixQt hcM (fixQt_eq_of_smithE8E34a h34a S hw hU hc hcM hcQ)
      hbQ hfix).symm
  have hbt := hcomm_b ht htM htQ hAt hwt
  have hbu := hcomm_b hu huM huQ hAu hwu
  have hbK : b ∈ K := hQK (mem_inf.mpr ⟨hbQ, mem_cent2.mpr ⟨hbt, hbu⟩⟩)
  obtain ⟨hb, rfl⟩ := isConj_iff.mp hbD
  have hyQb : hb⁻¹ * (g * S.z * g⁻¹) * hb ∈ S.QG := by
    have hQ : g⁻¹ * (hb * S.z * hb⁻¹) * g ∈ S.QG := (mem_Qa_iff S g _).mp hbQa
    refine mem_Qa_symm S hQ fun e => hyQ ?_
    rw [← e]
    exact hbQ
  have hyb : g * S.z * g⁻¹ ≠ hb * S.z * hb⁻¹ := fun e => hyQ (e ▸ hbQ)
  obtain ⟨q, hqt, hqu, hq⟩ := exists_conj_eq_mul_of_mem_Qa hE S hw hU ht hu htu hbt hbu hyD hyQb
    hyb hyt hyu
  have hqH : q ∈ cent2 t u := mem_cent2.mpr ⟨hqt, hqu⟩
  have hby : hb * S.z * hb⁻¹ * (g * S.z * g⁻¹) ∈ K := hq ▸ hnK q hqH _ hbK
  have := K.mul_mem (K.inv_mem hbK) hby
  rwa [inv_mul_cancel_left] at this

theorem card_eq_two_of_isPGroup_E8 {K : Type} [Group K] [Finite K] [IsSimpleGroup K]
    (hp : IsPGroup 2 K) : Nat.card K = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent K := hp.isNilpotent
  letI : CommGroup K := instCommGroupOfIsSimpleGroupOfIsNilpotent
  have hpr : (Nat.card K).Prime := IsSimpleGroup.prime_card
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hp
  rw [hn] at hpr ⊢
  rcases n with _ | n
  · exact absurd hpr (by norm_num)
  · rcases n with _ | n
    · rfl
    · exfalso
      have hd : 2 ∣ 2 ^ (n + 1 + 1) := dvd_pow_self 2 (by omega)
      rcases hpr.eq_one_or_self_of_dvd 2 hd with h | h
      · norm_num at h
      · have : 4 ≤ 2 ^ (n + 1 + 1) := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (n + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega

theorem toMbar_injective_of_simple_E8 (S : Setting G) {K : Subgroup G} (hKM : K ≤ S.M)
    [IsSimpleGroup K] (h2 : 2 < Nat.card K) : Function.Injective (SMH.toMbar S hKM) := by
  have : Finite S.Mbar := Bridge.finite_Mbar S
  have hker : (SMH.toMbar S hKM).ker = ⊥ := by
    rcases (SMH.toMbar S hKM).normal_ker.eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hKQ : ∀ k : K, (k : G) ∈ S.QG := fun k => by
        have h1 : k ∈ (SMH.toMbar S hKM).ker := by rw [h]; exact mem_top _
        rw [MonoidHom.mem_ker] at h1
        exact (S.ρ_eq_one_iff ⟨k, hKM k.2⟩).mp (congrArg Subtype.val h1)
      have hp : IsPGroup 2 K := fun k => by
        obtain ⟨n, hn⟩ := S.isPGroup_QG ⟨k, hKQ k⟩
        exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
      rw [card_eq_two_of_isPGroup_E8 hp] at h2
      exact lt_irrefl _ h2
  exact (MonoidHom.ker_eq_bot_iff _).mp hker

theorem card_mul_card_perpLevi_le (S : Setting G) (ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2)))
    {C : Subgroup G} (hCM : C ≤ S.M)
    (hI : ∀ γ ∈ perpRoots .E7, ∃ y ∈ C, ∃ hyM : y ∈ S.M,
      ψ (mbarPt S hyM) = pinnedElt .E7 γ (1 : ZMod 2)) :
    Nat.card ↥(S.QG ⊓ C) * Nat.card ↥(perpLevi .E7 (ZMod 2)) ≤ Nat.card C := by
  have : Finite S.Mbar := Bridge.finite_Mbar S
  obtain ⟨r, hr⟩ : ∃ r : C →* ↥(adjointGroup .E7 (ZMod 2)),
      ∀ c : C, r c = ψ (mbarPt S (hCM c.2)) :=
    ⟨ψ.toMonoidHom.comp (SMH.toMbar S hCM), fun c => rfl⟩
  have hrker : ∀ c : C, c ∈ r.ker ↔ (c : G) ∈ S.QG := fun c => by
    rw [MonoidHom.mem_ker, hr, ← map_one ψ]
    exact ⟨fun h => (mbarPt_eq_one_iff S (hCM c.2)).mp (ψ.injective h),
      fun h => congrArg ψ ((mbarPt_eq_one_iff S (hCM c.2)).mpr h)⟩
  have hker : Nat.card ↥(S.QG ⊓ C) ≤ Nat.card r.ker := by
    refine Nat.card_le_card_of_injective
      (fun q => ⟨⟨q.1, (mem_inf.mp q.2).2⟩, (hrker _).mpr (mem_inf.mp q.2).1⟩) fun a b hab => ?_
    exact Subtype.ext (congrArg (fun w : r.ker => ((w : C) : G)) hab)
  have hD : perpLevi .E7 (ZMod 2) ≤ r.range := by
    refine perpLevi_le_of_forall_mem _ fun γ hγ => ?_
    obtain ⟨y, hyC, hyM, hψy⟩ := hI γ hγ
    exact ⟨⟨y, hyC⟩, by rw [hr]; exact hψy⟩
  have hrange : Nat.card ↥(perpLevi .E7 (ZMod 2)) ≤ Nat.card r.range :=
    Subgroup.card_le_of_le hD
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup r.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange r).toEquiv] at h
  rw [h, mul_comm]
  exact Nat.mul_le_mul hrange hker

theorem nonempty_mulEquiv_Mbar_of_card_centralizer (S : Setting G)
    {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))} (h4 : SmithE8Clause4 S ψ)
    {K : Subgroup G} (hKM : K ≤ S.M) [IsSimpleGroup K] (h2 : 2 < Nat.card K)
    {x : G} (hxK : x ∈ K) (hx : IsConj S.z x) (hxQ : x ∉ S.QG)
    (hcard : 2 ^ 33 * Nat.card ↥(perpLevi .E7 (ZMod 2)) ≤
      Nat.card ↥(K ⊓ centralizer ({x} : Set G))) :
    Nonempty (K ≃* S.Mbar) := by
  classical
  have hinj := toMbar_injective_of_simple_E8 S hKM h2
  obtain ⟨ι, hι⟩ : ∃ ι : K →* ↥(adjointGroup .E7 (ZMod 2)),
      ∀ k : K, ι k = ψ (mbarPt S (hKM k.2)) :=
    ⟨ψ.toMonoidHom.comp (SMH.toMbar S hKM), fun k => rfl⟩
  have hιinj : Function.Injective ι := fun a b hab => by
    rw [hι, hι] at hab
    exact hinj (by
      have := ψ.injective hab
      exact this)
  have hxM : x ∈ S.M := hKM hxK
  have hrx : IsRootInvol (ι ⟨x, hxK⟩) := by
    rw [hι]
    exact h4 x hxM hx hxQ
  let f : ↥(K ⊓ centralizer ({x} : Set G)) →
      ↥(Subgroup.centralizer ({ι ⟨x, hxK⟩} : Set ↥(adjointGroup .E7 (ZMod 2)))) := fun a =>
    ⟨ι ⟨a, (mem_inf.mp a.2).1⟩, by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (mem_centralizer_singleton_iff.mp (mem_inf.mp a.2).2)⟩
  have hf : Function.Injective f := fun a b hab => by
    have h1 := hιinj (congrArg Subtype.val hab)
    exact Subtype.ext (congrArg (fun w : K => (w : G)) h1)
  have hfs : Function.Surjective f := by
    refine (Function.Injective.bijective_of_nat_card_le hf ?_).2
    exact (card_centralizer_le_of_isRootInvol hrx).trans hcard
  have hJ : ∀ g : ↥(adjointGroup .E7 (ZMod 2)), g * ι ⟨x, hxK⟩ = ι ⟨x, hxK⟩ * g → g ∈ ι.range := by
    intro g hg
    obtain ⟨a, ha⟩ := hfs ⟨g, Subgroup.mem_centralizer_singleton_iff.mpr hg⟩
    exact ⟨⟨a, (mem_inf.mp a.2).1⟩, congrArg Subtype.val ha⟩
  haveI : IsSimpleGroup ι.range := (MonoidHom.ofInjective hιinj).symm.isSimpleGroup
  have h2' : 2 < Nat.card ι.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv]
    exact h2
  have htop := eq_top_of_simple_of_centralizer_le h2' hrx hJ
  have hsurj : Function.Surjective ι := fun g => by
    have : g ∈ ι.range := by rw [htop]; exact mem_top g
    exact this
  exact ⟨(MulEquiv.ofBijective ι ⟨hιinj, hsurj⟩).trans ψ.symm⟩

theorem exists_N_std (hE : SmithE8E23a) (h33 : SmithE8E33) (h34a : SmithE8E34a)
    (h34b : SmithE8E34b) (hLoc : SmithE8LocalInput) (hF : E23FourFacts8) [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    {φ : S.Qt ≃ₗ[ZMod 2] (Fin e7Data.d →₀ ZMod 2)}
    {ψ : S.Mbar ≃* ↥(adjointGroup .E7 (ZMod 2))} (hE0 : SmithE8Equiv S φ ψ)
    (h2a : ∀ c : G, IsConj S.z c → c ∈ S.QG → c ≠ S.z → φ (S.cl c) ∈ weightVec)
    (h4 : SmithE8Clause4 S ψ)
    (h5 : ∀ r : ↥(adjointGroup .E7 (ZMod 2)), IsRootInvol r →
      ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧ ψ (mbarPt S hx) = r)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) (htu : orderOf (t * u) = 3)
    (hψt : ψ (mbarPt S htM) = xT) (hψu : ψ (mbarPt S huM) = xTn) :
    ∃ N : Subgroup G, S.z ∈ N ∧ (∀ n ∈ N, Commute n t ∧ Commute n u) ∧
      Nonempty (N ≃* S.Mbar) := by
  classical
  obtain ⟨K, hKH, hzK, hKs, hQK, hconjK, hnK⟩ :=
    exists_simple_le_cent2 hE S hw hU ht hu htM huM htQ huQ htu
  obtain ⟨-, hcard33, -, -, -⟩ := hE G S hw hU t u ht hu htM huM htQ huQ htu
  have hAt : Acts S φ t xT := by
    have := acts_of_equiv hE0 htM
    rwa [hψt] at this
  have hAu : Acts S φ u xTn := by
    have := acts_of_equiv hE0 huM
    rwa [hψu] at this
  have hlift : ∀ γ ∈ perpRoots .E7, ∃ y ∈ K, ∃ hyM : y ∈ S.M,
      ψ (mbarPt S hyM) = pinnedElt .E7 γ (1 : ZMod 2) := by
    intro γ hγ
    obtain ⟨hrt, hru⟩ := (commute_xT_xTn_iff _).2 (pinnedElt_mem_perpLevi hγ 1)
    obtain ⟨y, hyM, hyD, hyQ, hyt, hyu, hψy⟩ := exists_lift h34a h34b hLoc hw hU h5 ht hu htM huM
      htQ htu hψt hψu (isRootInvol_pinnedElt hγ.1) hrt hru
    obtain ⟨w, hwW, hEw, hwV⟩ := exists_inComm_mem_V0 hγ
    have hAy : Acts S φ y (pinnedElt .E7 γ (1 : ZMod 2)) := by
      have := acts_of_equiv hE0 hyM
      rwa [hψy] at this
    exact ⟨y, mem_K_of_lift hF h33 h34a h34b hE S hw hU hE0 h2a ht hu htM huM htQ huQ htu hAt hAu
      hQK hnK hyD hyM hyQ hyt hyu (isRootInvol_pinnedElt hγ.1) hAy hwW hEw hwV, hyM, hψy⟩
  have hCM : K ⊓ centralizer ({S.z} : Set G) ≤ S.M := inf_le_right
  have hcardC : 2 ^ 33 * Nat.card ↥(perpLevi .E7 (ZMod 2)) ≤
      Nat.card ↥(K ⊓ centralizer ({S.z} : Set G)) := by
    have hb := card_mul_card_perpLevi_le S ψ hCM fun γ hγ => by
      obtain ⟨y, hyK, hyM, hψy⟩ := hlift γ hγ
      exact ⟨y, mem_inf.mpr ⟨hyK, hyM⟩, hyM, hψy⟩
    have hQ : 2 ^ 33 ≤ Nat.card ↥(S.QG ⊓ (K ⊓ centralizer ({S.z} : Set G))) := by
      rw [← hcard33]
      refine Subgroup.card_le_of_le fun q hq => ?_
      exact mem_inf.mpr ⟨(mem_inf.mp hq).1, mem_inf.mpr ⟨hQK hq, S.QG_le_M (mem_inf.mp hq).1⟩⟩
    exact (Nat.mul_le_mul_right _ hQ).trans hb
  obtain ⟨g, hg⟩ := isConj_iff.mp ht
  obtain ⟨f, hf⟩ : ∃ f : G →* G, f = (MulAut.conj g⁻¹).toMonoidHom := ⟨_, rfl⟩
  have hfinj : Function.Injective f := by rw [hf]; exact (MulAut.conj g⁻¹).injective
  have hfapp : ∀ a : G, f a = g⁻¹ * a * g := fun a => by
    simp [hf, MulAut.conj_apply]
  have hK'M : K.map f ≤ S.M := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hfapp, mem_centralizer_singleton_iff]
    have hkt := (mem_cent2.mp (hKH hk)).1
    rw [← hg] at hkt
    simp only [Commute, SemiconjBy] at hkt
    calc g⁻¹ * k * g * S.z = g⁻¹ * (k * (g * S.z * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * S.z * g⁻¹) * k) * g := by rw [hkt]
      _ = S.z * (g⁻¹ * k * g) := by group
  haveI : IsSimpleGroup (K.map f) := (Subgroup.equivMapOfInjective K f hfinj).symm.isSimpleGroup
  have hxK : g⁻¹ * S.z * g ∈ K.map f := ⟨S.z, hzK, hfapp _⟩
  have hx : IsConj S.z (g⁻¹ * S.z * g) := isConj_iff.mpr ⟨g⁻¹, by group⟩
  have hxQ : g⁻¹ * S.z * g ∉ S.QG := fun h => htQ (by
    have := SME.mem_Qa_symm S (g := g) (k := 1) (by simpa using h) (by
      rw [hg]
      simpa using fun e : S.z = t => htQ (e ▸ S.z_mem_QG))
    simpa [hg] using this)
  have hcard' : 2 ^ 33 * Nat.card ↥(perpLevi .E7 (ZMod 2)) ≤
      Nat.card ↥(K.map f ⊓ centralizer ({g⁻¹ * S.z * g} : Set G)) := by
    refine hcardC.trans (Nat.card_le_card_of_injective
      (fun c => ⟨f c, mem_inf.mpr ⟨⟨c, (mem_inf.mp c.2).1, rfl⟩, ?_⟩⟩) fun a b hab => ?_)
    · rw [hfapp, mem_centralizer_singleton_iff]
      have hc := mem_centralizer_singleton_iff.mp (mem_inf.mp c.2).2
      calc g⁻¹ * (c : G) * g * (g⁻¹ * S.z * g) = g⁻¹ * ((c : G) * S.z) * g := by group
        _ = g⁻¹ * (S.z * c) * g := by rw [hc]
        _ = g⁻¹ * S.z * g * (g⁻¹ * c * g) := by group
    · exact Subtype.ext (hfinj (congrArg Subtype.val hab))
  have h2K : 2 < Nat.card (K.map f) := by
    refine lt_of_lt_of_le ?_ (hcard'.trans (Subgroup.card_le_of_le inf_le_left))
    have : 1 ≤ Nat.card ↥(perpLevi .E7 (ZMod 2)) := Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne'
    calc 2 < 2 ^ 33 * 1 := by norm_num
      _ ≤ 2 ^ 33 * Nat.card ↥(perpLevi .E7 (ZMod 2)) := Nat.mul_le_mul_left _ this
  obtain ⟨e⟩ := nonempty_mulEquiv_Mbar_of_card_centralizer S h4 hK'M h2K hxK hx hxQ hcard'
  exact ⟨K, hzK, fun n hn => mem_cent2.mp (hKH hn),
    ⟨(Subgroup.equivMapOfInjective K f hfinj).trans e⟩⟩

theorem smithE8E261_of (h34a : SmithE8E34a) (h34b : SmithE8E34b) (hLoc : SmithE8LocalInput)
    (hE : SmithE8E23a) (hC : SmithE8Compat) (h33 : SmithE8E33) (hF : E23FourFacts8) :
    SmithE8E261 := by
  intro G _ _ _ S hw hU t u ht hu htM huM htQ huQ htu
  obtain ⟨φ, ψ, ⟨hE0, h2a, h2b, h3⟩, h4, h5⟩ := hC G S hw hU
  have hrt := h4 t htM ht htQ
  have hru := h4 u huM hu huQ
  have hord := orderOf_psi_mul (ψ := ψ) htM huM htu
  obtain ⟨g, hg1, hg2⟩ := exists_conj_opposite hrt hru hord
  obtain ⟨m, hmM, hm⟩ := exists_mbarPt_eq S ψ g
  have htM' : m * t * m⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hmM htM) (S.M.inv_mem hmM)
  have huM' : m * u * m⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hmM huM) (S.M.inv_mem hmM)
  have hψt' : ψ (mbarPt S htM') = xT := by
    rw [mbarPt_conj S hmM htM, map_mul, map_mul, map_inv, hm]
    exact hg1
  have hψu' : ψ (mbarPt S huM') = xTn := by
    rw [mbarPt_conj S hmM huM, map_mul, map_mul, map_inv, hm]
    exact hg2
  have hconjQ : ∀ {x : G}, x ∉ S.QG → m * x * m⁻¹ ∉ S.QG := fun hx h =>
    hx ((conj_mem_QG_iff_E8 S hmM).mp h)
  have h3m : orderOf (m * t * m⁻¹ * (m * u * m⁻¹)) = 3 := by
    rw [show m * t * m⁻¹ * (m * u * m⁻¹) = MulAut.conj m (t * u) by
      rw [MulAut.conj_apply]; group, MulEquiv.orderOf_eq]
    exact htu
  obtain ⟨N', hzN', hN'c, ⟨e'⟩⟩ := exists_N_std hE h33 h34a h34b hLoc hF S hw hU hE0 h2a h4 h5
    (ht.trans (isConj_iff.mpr ⟨m, rfl⟩)) (hu.trans (isConj_iff.mpr ⟨m, rfl⟩)) htM' huM'
    (hconjQ htQ) (hconjQ huQ) h3m hψt' hψu'
  have hmz : m * S.z = S.z * m := mem_centralizer_singleton_iff.mp hmM
  refine ⟨N'.map (MulAut.conj m⁻¹).toMonoidHom, ⟨S.z, hzN', ?_⟩, ?_, ?_⟩
  · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc m⁻¹ * S.z * m⁻¹⁻¹ = m⁻¹ * (S.z * m) := by group
      _ = m⁻¹ * (m * S.z) := by rw [hmz]
      _ = S.z := by group
  · rintro _ ⟨n, hn, rfl⟩
    obtain ⟨h1, h2⟩ := hN'c n hn
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨?_, ?_⟩
    · have := (commute_conj_iff_E8 m⁻¹ n (m * t * m⁻¹)).2 h1
      simpa [mul_assoc] using this
    · have := (commute_conj_iff_E8 m⁻¹ n (m * u * m⁻¹)).2 h2
      simpa [mul_assoc] using this
  · exact LieModel.of_mulEquiv
      ((Subgroup.equivMapOfInjective N' (MulAut.conj m⁻¹).toMonoidHom
        (MulAut.conj m⁻¹).injective).symm.trans e').symm hU

end CFSG.GF2Type.SmithTypeE.E8
