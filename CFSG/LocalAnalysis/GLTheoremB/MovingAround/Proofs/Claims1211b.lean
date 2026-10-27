module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1211
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1211b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1211
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1211
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.AltFacts
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open scoped commutatorElement

section PermTransvection

open Equiv Equiv.Perm
open scoped Classical

variable {Fh Bh : Subgroup (Perm (Fin 13))} {c₀ : Perm (Fin 13)}

theorem exists_mul_mem_of_orbit (h : Cfg13 Fh Bh c₀) {Zh : Subgroup (Perm (Fin 13))}
    (hZle : Zh ≤ Fh ⊔ Bh) (hZorb : ∃ i : Fin 13, Set.ncard (MulAction.orbit Zh i) = 9)
    {f : Perm (Fin 13)} (hf : f ∈ Fh) : ∃ c ∈ Bh, f * c ∈ Zh := by
  obtain ⟨i, hi⟩ := hZorb
  have hsub : ∀ k ∈ MulAction.orbit Zh i, (i ∈ moved Fh ↔ k ∈ moved Fh) := by
    rintro _ ⟨x, rfl⟩
    exact h.moved_pres (hZle x.2)
  have himoved : i ∈ moved Fh := by
    by_contra hni
    have hsubc : MulAction.orbit Zh i ⊆ {j : Fin 13 | ∀ g ∈ Fh, g j = j} := by
      intro k hk g hg
      have : k ∉ moved Fh := fun hkm => hni ((hsub k hk).2 hkm)
      exact not_moved_fix' hg this
    have := Set.ncard_le_ncard hsubc (Set.toFinite _)
    rw [hi, h.fix4] at this
    omega
  have horbeq : MulAction.orbit Zh i = moved Fh := by
    refine Set.eq_of_subset_of_ncard_le ?_ (by rw [hi, h.card_moved]) (Set.toFinite _)
    intro k hk
    exact (hsub k hk).1 himoved
  have hfi : f i ∈ moved Fh := orb_mem' h.comm himoved ⟨f, hf⟩
  have hfi' : f i ∈ MulAction.orbit Zh i := horbeq ▸ hfi
  obtain ⟨⟨x, hxZ⟩, hx⟩ := hfi'
  have hxi : x i = f i := hx
  obtain ⟨f', hf', c, hc, rfl⟩ := h.exists_mul (hZle hxZ)
  rw [Perm.mul_apply, h.bfix c hc i himoved] at hxi
  obtain ⟨u, -, hu⟩ := h.reg i (f i) himoved hfi
  have h1 : f' = u := hu f' ⟨hf', hxi⟩
  have h2 : f = u := hu f ⟨hf, rfl⟩
  exact ⟨c, hc, (h1.trans h2.symm) ▸ hxZ⟩

theorem perm_transvection (h : Cfg13 Fh Bh c₀) {Zh : Subgroup (Perm (Fin 13))}
    (hZle : Zh ≤ Fh ⊔ Bh) (hZcard : Nat.card Zh ≤ 9)
    (hZorb : ∃ i : Fin 13, Set.ncard (MulAction.orbit Zh i) = 9) :
    ∃ σ ∈ alternatingGroup (Fin 13), σ ^ 3 = 1 ∧ (∀ x ∈ Zh, σ * x * σ⁻¹ ∈ Zh) ∧
      ∃ x ∈ Zh, σ * x * σ⁻¹ ≠ x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hZ9, -⟩ := h.zh_regular hZle hZcard hZorb
  obtain ⟨w, hwZF, hw1⟩ := h.exists_w hZle hZ9
  have hwZ : w ∈ Zh := hwZF.1
  have hwF : w ∈ Fh := hwZF.2
  obtain ⟨f₀, hf₀, hfw⟩ : ∃ f₀ ∈ Fh, f₀ ∉ Subgroup.zpowers w := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (fun x hx => hall x hx : Fh ≤ Subgroup.zpowers w)
    rw [h.card_Fh, Nat.card_zpowers] at h1
    have h2 : orderOf w ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (h.three w hwF))
    omega
  letI : CommGroup ↥Fh :=
    { (inferInstance : Group ↥Fh) with mul_comm := fun x y => Subtype.ext (h.comm x x.2 y y.2) }
  have hF3 : ∀ x : ↥Fh, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using h.three x x.2)
  obtain ⟨α, hαf, hα3, hαg⟩ := exists_transvection (H := ↥Fh) hF3 h.card_Fh
    (f := ⟨f₀, hf₀⟩) (w := ⟨w, hwF⟩) (fun h1 => hw1 (congrArg Subtype.val h1)) (by
      intro hmem
      apply hfw
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
      exact Subgroup.mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩)
  obtain ⟨ω, hω⟩ := h.exists_moved
  set σ := sigmaOf' h.comm h.reg hω α with hσ
  have hσconj : ∀ g : ↥Fh, σ * (g : Perm (Fin 13)) * σ⁻¹ = ((α g : ↥Fh) : Perm (Fin 13)) :=
    fun g => sigma'_conj h.comm h.reg hω α g
  have hσc : ∀ c' ∈ Bh, σ * c' = c' * σ := fun c' hc' =>
    sigma'_commute_of_fix h.comm h.reg hω α (h.bfix c' hc')
  have hσ3 : σ ^ 3 = 1 := sigma'_pow_three h.comm h.reg hω α hα3
  have hσalt : σ ∈ alternatingGroup (Fin 13) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h1 := congrArg Equiv.Perm.sign hσ3
    rw [map_pow, map_one] at h1
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
    · exact h2
    · rw [h2] at h1
      exact absurd h1 (by decide)
  have hconjFB : ∀ (g : ↥Fh), ∀ c' ∈ Bh, σ * ((g : Perm (Fin 13)) * c') * σ⁻¹ =
      ((α g : ↥Fh) : Perm (Fin 13)) * c' := by
    intro g c' hc'
    have e : σ * ((g : Perm (Fin 13)) * c') * σ⁻¹ = (σ * g * σ⁻¹) * (σ * c' * σ⁻¹) := by group
    rw [e, hσconj g, hσc c' hc']
    group
  refine ⟨σ, hσalt, hσ3, ?_, ?_⟩
  · intro x hx
    obtain ⟨f, hf, c', hc', rfl⟩ := h.exists_mul (hZle hx)
    have h1 := hconjFB ⟨f, hf⟩ c' hc'
    simp only at h1
    rw [h1]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hαg ⟨f, hf⟩)
    have hk' : (f : Perm (Fin 13))⁻¹ * ((α ⟨f, hf⟩ : ↥Fh) : Perm (Fin 13)) = w ^ k := by
      have := congrArg Subtype.val hk
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] at this
      exact this.symm
    have hαf' : ((α ⟨f, hf⟩ : ↥Fh) : Perm (Fin 13)) = f * w ^ k := by
      rw [← hk']
      group
    have hwk : w ^ k ∈ Fh := Fh.zpow_mem hwF k
    have hcomm : c' * w ^ k = w ^ k * c' := (h.fb_comm _ hwk c' hc').symm
    have e : ((α ⟨f, hf⟩ : ↥Fh) : Perm (Fin 13)) * c' = (f * c') * w ^ k := by
      rw [hαf', mul_assoc, mul_assoc, hcomm]
    rw [e]
    exact Zh.mul_mem hx (Zh.zpow_mem hwZ k)
  · obtain ⟨c, hc, hxZ⟩ := exists_mul_mem_of_orbit h hZle hZorb hf₀
    refine ⟨f₀ * c, hxZ, ?_⟩
    have h1 := hconjFB ⟨f₀, hf₀⟩ c hc
    simp only at h1
    rw [h1, hαf]
    intro heq
    apply hw1
    have h2 : (f₀ * w) * c = f₀ * c := by simpa using heq
    have h3 : f₀ * w = f₀ * 1 := by rw [mul_one]; exact mul_right_cancel h2
    exact mul_left_cancel h3

end PermTransvection

section A0bar

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_pow_three {Γ : Type} [Group Γ] {H : Subgroup Γ} {x : Γ} (hx3 : x ^ 3 = 1)
    (hH : ∀ n ∈ H, x * n * x⁻¹ ∈ H) : x ∈ Subgroup.normalizer (H : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨hH n, fun hn => ?_⟩
  have h1 := hH _ (hH _ hn)
  have e : x * (x * (x * n * x⁻¹) * x⁻¹) * x⁻¹ = x ^ 3 * n * (x ^ 3)⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc]
  rw [e, hx3, one_mul, inv_one, mul_one] at h1
  exact h1

theorem claim1211_A0bar_holds : Claim1211_A0bar := by
  intro G _ _ m p B M E A N D h K hK
  obtain ⟨hcom, hp3, -, -, hAK, φ, hOrb, F, a, hF⟩ := hK
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hAN : A ≤ N := by
    intro x hx
    apply h.hD
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun d hd => ?_)
    exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨d, h.plane.1 hd⟩ ⟨x, hx⟩)
  obtain ⟨hEk, hFix, hreg, haA, hAeq, -, hBth⟩ := hF
  set ι : ↥(barX 3 N K) →* Equiv.Perm (Fin 13) :=
    (alternatingGroup (Fin 13)).subtype.comp φ.toMonoidHom with hι
  have hιinj : Function.Injective ι := Subtype.val_injective.comp φ.injective
  obtain ⟨c₀, hcfg, hAmap⟩ := config_unpack ι hιinj _ _ rfl rfl hAN hAK hEk haA hAeq hFix hreg hBth
  have hUN : E ⊓ A ≤ N := inf_le_right.trans hAN
  have hbarU : barX 3 N (E ⊓ A) ≤ barX 3 N K :=
    (Lemma1210.barX_mono_left (inf_le_right : E ⊓ A ≤ A)).trans hAK
  set Zh : Subgroup (Equiv.Perm (Fin 13)) := ((barX 3 N (E ⊓ A)).subgroupOf (barX 3 N K)).map ι
    with hZh
  have hZle : Zh ≤ ((barX 3 N A).subgroupOf (barX 3 N K)).map ι :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2
      (Lemma1210.barX_mono_left (inf_le_right : E ⊓ A ≤ A) (Subgroup.mem_subgroupOf.1 hx))
  rw [hAmap] at hZle
  have hUe : IsElemAbelian 3 (E ⊓ A) := Lemma1112.isElemAbelian_of_le hAel inf_le_right
  have hUcard : Nat.card ↥(E ⊓ A) = 9 := by
    rw [Lemma1112.card_eq_pow_pRank hUe, hcom.2.1.2]
    norm_num
  have hZcard : Nat.card ↥Zh ≤ 9 := by
    rw [hZh, Subgroup.card_map_of_injective hιinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hbarU).toEquiv, Lemma1210.barX_eq_map]
    have h1 : Nat.card ↥(((E ⊓ A).subgroupOf N).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥N))) ∣
        Nat.card ↥((E ⊓ A).subgroupOf N) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥((E ⊓ A).subgroupOf N) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv, hUcard]
    rw [h2] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  obtain ⟨σ, hσalt, hσ3, hσN, x, hxZ, hσx⟩ := perm_transvection hcfg hZle hZcard hOrb
  set y : ↥(barX 3 N K) := φ.symm ⟨σ, hσalt⟩ with hy
  have hιy : ι y = σ := by
    show ((φ (φ.symm ⟨σ, hσalt⟩) : alternatingGroup (Fin 13)) : Equiv.Perm (Fin 13)) = σ
    rw [MulEquiv.apply_symm_apply]
  have hy3 : y ^ 3 = 1 := hιinj (by rw [map_pow, hιy, hσ3, map_one])
  have hconj : ∀ u : ↥(barX 3 N K), u ∈ (barX 3 N (E ⊓ A)).subgroupOf (barX 3 N K) →
      y * u * y⁻¹ ∈ (barX 3 N (E ⊓ A)).subgroupOf (barX 3 N K) := by
    intro u hu
    have h1 := hσN (ι u) (Subgroup.mem_map_of_mem ι hu)
    rw [← hιy, ← map_inv, ← map_mul, ← map_mul] at h1
    obtain ⟨v, hv, hveq⟩ := Subgroup.mem_map.1 h1
    rwa [← hιinj hveq]
  refine ⟨(y : ↥N ⧸ GLAPPrimeCore 3 ↥N), ⟨1, ?_⟩, ?_, ?_⟩
  · rw [pow_one, ← Subgroup.coe_pow, hy3, Subgroup.coe_one]
  · refine mem_normalizer_of_pow_three (by rw [← Subgroup.coe_pow, hy3, Subgroup.coe_one]) ?_
    intro n hn
    have h1 := hconj ⟨n, hbarU hn⟩ (Subgroup.mem_subgroupOf.2 hn)
    exact Subgroup.mem_subgroupOf.1 h1
  · intro hc
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hxZ
    apply hσx
    have h1 : (u : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) =
        (y : ↥N ⧸ GLAPPrimeCore 3 ↥N) * (u : ↥N ⧸ GLAPPrimeCore 3 ↥N) :=
      (Subgroup.mem_centralizer_iff.1 hc) _ (Subgroup.mem_subgroupOf.1 hu)
    have h2 : u * y = y * u := Subtype.ext h1
    rw [← hιy, ← map_inv, ← map_mul, ← map_mul, ← h2]
    congr 1
    group

theorem cTilde_isPConstrained (hI : Input24_5) :
    ∀ {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
      (h : Cex127 G m p B M E A N D) {K : Subgroup G} (hK : AlphaData1211 p M E A N K) {z : G}
      (hz : z ∈ A ∧ z ≠ 1) (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M),
      CFSG.ABGLocalTools.IsPConstrained 3 (↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z)) :=
  cTilde_isPConstrained_of_A0bar hI claim1211_A0bar_holds

end A0bar

section Cover

variable {X : Type} [Group X] [Finite X] {p : ℕ}

structure CoverData (p : ℕ) (X : Type) [Group X] [Finite X] (S Mb : Subgroup X) : Prop where
  syl : IsSylowIn p ⊤ S
  le : S ≤ Mb
  gamma : ∀ Q : Subgroup X, Q ≤ S → 4 ≤ CFSG.Open.pRank p Q → Subgroup.normalizer (Q : Set X) ≤ Mb
  gamma2 : ∀ Eb : Subgroup X, IsEkIn p 4 S Eb → GLBCore p 2 Eb ≤ Mb
  rank5 : ∃ H : Subgroup X, H ≤ S ∧ IsElemAbelian p H ∧ Nat.card H = p ^ 5
  notTop : ¬ (⊤ : Subgroup X) ≤ Mb

@[expose] def toSylow {S : Subgroup X} (hS : IsSylowIn p ⊤ S) : Sylow p X where
  toSubgroup := S
  isPGroup' := hS.2.1
  is_maximal' := fun hQ hle => hS.2.2 _ le_top hQ hle

theorem top_le_normalizer {V : Subgroup X} (hV : V.Normal) :
    (⊤ : Subgroup X) ≤ Subgroup.normalizer (V : Set X) := by
  intro x _
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => hV.conj_mem n hn x, fun hn => ?_⟩
  have h := hV.conj_mem _ hn x⁻¹
  simpa [mul_assoc] using h

theorem not_dvd_relIndex_of_isSylowIn [Fact p.Prime] {O R : Subgroup X} (h : IsSylowIn p O R) :
    ¬ p ∣ R.relIndex O := by
  obtain ⟨S', hS'⟩ := exists_sylow_of_isSylowIn h
  have e : R.subgroupOf O = (S' : Subgroup ↥O) := by
    rw [← hS']
    exact Subgroup.comap_map_eq_self_of_injective O.subtype_injective _
  rw [Subgroup.relIndex, e]
  exact S'.not_dvd_index

theorem isSylowIn_of_not_dvd [Fact p.Prime] {Q L : Subgroup X} (hQL : Q ≤ L) (hQ : IsPGroup p Q)
    (hidx : ¬ p ∣ Q.relIndex L) : IsSylowIn p L Q := by
  refine ⟨hQL, hQ, fun Q' hQ'L hQ'p hQQ' => ?_⟩
  have h := Subgroup.relIndex_mul_relIndex Q Q' L hQQ' hQ'L
  obtain ⟨k, hk⟩ := hQ'p.exists_card_eq
  have hdvd : Q.relIndex Q' ∣ p ^ k := by
    rw [← hk, Subgroup.relIndex]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).1 hdvd
  have hj0 : j = 0 := by
    by_contra hj0
    apply hidx
    rw [← h, hj]
    exact Dvd.dvd.mul_right (dvd_pow_self p hj0) _
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact le_antisymm hj hQQ'

variable {S Mb : Subgroup X}

theorem CoverData.cover_pGroup [Fact p.Prime] (hd : CoverData p X S Mb) {U V : Subgroup X} [U.Normal]
    (hVn : V.Normal) (hUM : U ≤ Mb) (hV : IsPGroup p ↥(V.map (QuotientGroup.mk' U))) : V ≤ Mb := by
  intro v hv
  have hπs := QuotientGroup.mk'_surjective U
  haveI : (V.map (QuotientGroup.mk' U)).Normal := hVn.map _ hπs
  have hle := hV.le_sylow_of_normal ((toSylow hd.syl).mapSurjective hπs)
  have h1 := hle (Subgroup.mem_map_of_mem _ hv)
  rw [Sylow.coe_mapSurjective] at h1
  obtain ⟨s, hs, hsv⟩ := h1
  have h2 : s⁻¹ * v ∈ U := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hsv
    exact hsv
  have e : v = s * (s⁻¹ * v) := by group
  rw [e]
  exact Mb.mul_mem (hd.le hs) (hUM h2)

theorem CoverData.cover_pPrime [Fact p.Prime] (hd : CoverData p X S Mb) {U V : Subgroup X} [U.Normal]
    (hVn : V.Normal) (hUV : U ≤ V) (hUM : U ≤ Mb) (hV : ¬ p ∣ Nat.card ↥(V.map (QuotientGroup.mk' U))) :
    V ≤ Mb := by
  classical
  set π : X →* X ⧸ U := QuotientGroup.mk' U with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective U
  have hπker : ∀ x : X, π x = 1 ↔ x ∈ U := fun x => QuotientGroup.eq_one_iff x
  have hlift : ∀ v : X, π v ∈ Mb.map π → v ∈ Mb := by
    intro v hv
    obtain ⟨m', hm', hm'v⟩ := hv
    have h2 : m'⁻¹ * v ∈ U := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hm'v
      exact hm'v
    have e : v = m' * (m'⁻¹ * v) := by group
    rw [e]
    exact Mb.mul_mem hm' (hUM h2)
  have hUn : (U : Subgroup X).Normal := inferInstance
  have hSU : IsSylowIn p U (S ⊓ U) := isSylowIn_inf hd.syl le_top (top_le_normalizer hUn)
  obtain ⟨H, hHS, hHe, hHc⟩ := hd.rank5
  by_cases hHU : H ≤ U
  · have h4 : 4 ≤ CFSG.Open.pRank p (S ⊓ U) :=
      le_trans (by norm_num) (le_pRank_of_card (le_inf hHS hHU) hHe hHc)
    have hFr := le_sup_normalizer_inf hd.syl (le_top : U ≤ ⊤) (top_le_normalizer hUn)
    exact fun v _ => sup_le hUM (hd.gamma _ inf_le_left h4) (hFr (Subgroup.mem_top v))
  set Hb : Subgroup (X ⧸ U) := H.map π with hHb
  haveI : CFSG.IsElementaryAbelian p ↥Hb := (hHe.map π).isElementaryAbelian
  obtain ⟨h₀, hh₀H, hh₀U⟩ := Set.not_subset.1 hHU
  haveI : Nontrivial ↥Hb := ⟨⟨⟨π h₀, Subgroup.mem_map_of_mem π hh₀H⟩, 1, fun he =>
    hh₀U ((hπker h₀).1 (congrArg Subtype.val he))⟩⟩
  haveI hVbn : (V.map π).Normal := hVn.map π hπs
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (A := Hb)
    (V := V.map π) (le_top.trans (top_le_normalizer hVbn)) hV
  set f : ↥H →* ↥Hb := (π.comp H.subtype).codRestrict Hb fun h => Subgroup.mem_map_of_mem π h.2
    with hf
  have hfs : Function.Surjective f := by
    rintro ⟨_, ⟨h, hh, rfl⟩⟩
    exact ⟨⟨h, hh⟩, rfl⟩
  have key : ∀ B : Subgroup ↥Hb, B.index = p →
      V.map π ⊓ Subgroup.centralizer ((B.map Hb.subtype : Subgroup (X ⧸ U)) : Set (X ⧸ U)) ≤
        Mb.map π := by
    intro B hB vb hvb
    obtain ⟨hvbV, hvbC⟩ := Subgroup.mem_inf.1 hvb
    obtain ⟨v, -, rfl⟩ := Subgroup.mem_map.1 hvbV
    set L : Subgroup X := (B.map Hb.subtype).comap π with hL
    have hvL : v ∈ Subgroup.normalizer (L : Set X) :=
      Subgroup.le_normalizer_comap π (Subgroup.centralizer_le_normalizer _ hvbC)
    have hUL : U ≤ L := fun u hu => by
      show π u ∈ B.map Hb.subtype
      rw [(hπker u).2 hu]
      exact Subgroup.one_mem _
    have hLeq : L = U ⊔ (S ⊓ L) := by
      refine le_antisymm (fun l hl => ?_) (sup_le hUL inf_le_right)
      have hl' : π l ∈ B.map Hb.subtype := hl
      obtain ⟨b, hbB, hb⟩ := Subgroup.mem_map.1 hl'
      obtain ⟨h, hh, hhb⟩ := Subgroup.mem_map.1 b.2
      have hhL : h ∈ L := by
        show π h ∈ B.map Hb.subtype
        rw [hhb]
        exact ⟨b, hbB, rfl⟩
      have h2 : h⁻¹ * l ∈ U := by
        have : π h = π l := hhb.trans hb
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
        exact this
      have e2 : l = h * (h⁻¹ * l) := by group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hHS hh, hhL⟩) (Subgroup.mem_sup_left h2)
    have hQp : IsPGroup p ↥(S ⊓ L) := isPGroup_of_le' hd.syl.2.1 inf_le_left
    have hSyl : IsSylowIn p L (S ⊓ L) := by
      refine isSylowIn_of_not_dvd inf_le_right hQp ?_
      have h1 := CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal U (S ⊓ L)
      rw [← hLeq] at h1
      rw [h1, ← Subgroup.inf_relIndex_right, inf_assoc, inf_eq_right.2 hUL]
      exact not_dvd_relIndex_of_isSylowIn hSU
    have h4 : 4 ≤ CFSG.Open.pRank p (S ⊓ L) := by
      have hidx : (B.comap f).index = p := by rw [Subgroup.index_comap_of_surjective B hfs, hB]
      have hcard : Nat.card ↥(B.comap f) = p ^ 4 := by
        have h1 := (B.comap f).card_mul_index
        rw [hidx, hHc] at h1
        have hp0 : 0 < p := (Fact.out : p.Prime).pos
        have : Nat.card ↥(B.comap f) * p = p ^ 4 * p := by rw [h1]; ring
        exact Nat.eq_of_mul_eq_mul_right hp0 this
      have hle : (B.comap f).map H.subtype ≤ S ⊓ L := by
        rintro _ ⟨h, hh, rfl⟩
        refine ⟨hHS h.2, ?_⟩
        show π h ∈ B.map Hb.subtype
        exact ⟨f h, hh, rfl⟩
      refine le_pRank_of_card hle (hHe.mono (Subgroup.map_subtype_le _)) ?_
      rw [Subgroup.card_map_of_injective H.subtype_injective, hcard]
    obtain ⟨R', hR', hQR'⟩ := exists_isSylowIn_above' (X := Subgroup.normalizer (L : Set X))
      (inf_le_right.trans Subgroup.le_normalizer) hQp
    have hRL : R' ⊓ L = S ⊓ L :=
      hSyl.2.2 _ inf_le_right (isPGroup_of_le' hR'.2.1 inf_le_left) (le_inf hQR' inf_le_right)
    have hFr := le_sup_normalizer_inf hR' Subgroup.le_normalizer le_rfl
    rw [hRL] at hFr
    have hLM : L ≤ Mb := by
      rw [hLeq]
      exact sup_le hUM (inf_le_left.trans hd.le)
    exact Subgroup.mem_map_of_mem π (sup_le hLM (hd.gamma _ inf_le_left h4) (hFr hvL))
  intro v hv
  exact hlift v ((hgen.trans (iSup₂_le key)) (Subgroup.mem_map_of_mem π hv))

theorem CoverData.not_isPSolvable [Fact p.Prime] (hd : CoverData p X S Mb) :
    ¬ CFSG.HallHigman.IsPSolvable p X := by
  intro hsolv
  classical
  haveI : Finite (Subgroup X) :=
    Finite.of_injective (fun H : Subgroup X => (H : Set X)) SetLike.coe_injective
  obtain ⟨U, hU⟩ := (Set.toFinite {U : Subgroup X | U.Normal ∧ U ≤ Mb}).exists_maximal
    ⟨⊥, Subgroup.normal_bot, bot_le⟩
  obtain ⟨hUn, hUM⟩ := hU.prop
  haveI := hUn
  set π : X →* X ⧸ U := QuotientGroup.mk' U with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective U
  have hsep : CFSG.HallHigman.IsPiSeparable {q : Nat.Primes | q.val = p} (X ⧸ U) :=
    (CFSG.HallHigman.isPiSeparable_of_isPSolvable Fact.out hsolv).quotient U
  haveI : Finite (Subgroup (X ⧸ U)) :=
    Finite.of_injective (fun H : Subgroup (X ⧸ U) => (H : Set (X ⧸ U))) SetLike.coe_injective
  have hne : (⊤ : Subgroup (X ⧸ U)) ≠ ⊥ := by
    intro htop
    apply hd.notTop
    intro x _
    have : π x ∈ (⊥ : Subgroup (X ⧸ U)) := htop ▸ Subgroup.mem_top _
    exact hUM ((QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 this))
  obtain ⟨Nq, hN⟩ := (Set.toFinite {N : Subgroup (X ⧸ U) | N.Normal ∧ N ≠ ⊥}).exists_minimal
    ⟨⊤, Subgroup.normal_top, hne⟩
  obtain ⟨hNn, hNb⟩ := hN.prop
  haveI := hNn
  have hmin : ∀ K : Subgroup (X ⧸ U), K.Normal → K ≤ Nq → K = ⊥ ∨ K = Nq := by
    intro K hK hKN
    by_cases hKb : K = ⊥
    · exact Or.inl hKb
    · exact Or.inr (le_antisymm hKN (hN.le_of_le ⟨hK, hKb⟩ hKN))
  set V : Subgroup X := Nq.comap π with hV
  have hVn : V.Normal := hNn.comap π
  have hUV : U ≤ V := fun u hu => by
    show π u ∈ Nq
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).2 hu]
    exact Nq.one_mem
  have hVmap : V.map π = Nq := Subgroup.map_comap_eq_self_of_surjective hπs Nq
  have hVM : V ≤ Mb := by
    rcases CFSG.HallHigman.IsPiSeparable.minimal_normal hsep hNb hmin with h | h
    · refine hd.cover_pGroup hVn hUM ?_
      rw [hVmap]
      refine IsPGroup.of_card (n := (Nat.card ↥Nq).primeFactorsList.length) ?_
      exact Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hq hqd => h ⟨_, hq⟩ hqd
    · refine hd.cover_pPrime hVn hUV hUM ?_
      rw [hVmap]
      exact fun hdvd => h ⟨p, Fact.out⟩ hdvd rfl
  have hVU : V ≤ U := hU.le_of_ge ⟨hVn, hVM⟩ hUV
  apply hNb
  rw [← hVmap, eq_bot_iff]
  rintro _ ⟨v, hv, rfl⟩
  exact Subgroup.mem_bot.2 ((QuotientGroup.eq_one_iff v).2 (hVU hv))

end Cover

section Kernel

open CFSG.SectionRank.Ccomm (IsThompsonCritical)
open CFSG.OrderReductions.FrattiniAutomorphisms (quotientAutomorphism)

variable {p : ℕ} [Fact p.Prime]

abbrev omegaC (p : ℕ) {T : Type} [Group T] (C : Subgroup T) : Subgroup T :=
  (CFSG.omega₁ (G := ↥C) (p := p)).map C.subtype

theorem commutator_le_frattini {W : Type} [Group W] [Finite W] (hW : IsPGroup p W) :
    commutator W ≤ frattini W := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  exact CFSG.SectionRank.Ccomm.commutator_mem_frattini hW x y

theorem aut_eq_one_of_critical (hp2 : p ≠ 2) {T : Type} [Group T] [Finite T] (hT : IsPGroup p T)
    {C : Subgroup T} (hC : IsThompsonCritical C) (β : MulAut T) (hβ : (orderOf β).Coprime p)
    (hfix : ∀ w ∈ omegaC p C, w⁻¹ * β w ∈ ⁅omegaC p C, omegaC p C⁆) : β = 1 := by
  obtain ⟨hCchar, hCΦ, -, hCcen⟩ := hC
  haveI := hCchar
  haveI : (CFSG.omega₁ (G := ↥C) (p := p)).Characteristic := CFSG.omega₁_characteristic _
  set W := omegaC p C with hW
  have hWp : IsPGroup p ↥W := hT.to_subgroup W
  set βW := MulAut.characteristic W β with hβW
  have hβWker : βW ∈ (quotientAutomorphism (frattini ↥W)).ker := by
    rw [MonoidHom.mem_ker]
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini ↥W) q
    rw [CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism_apply, MulAut.one_apply,
      QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    have h1 := hfix x x.2
    rw [← Subgroup.map_subtype_commutator] at h1
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 h1
    have hc' : c = x⁻¹ * βW x := Subtype.ext (by
      show W.subtype c = _
      rw [hce]
      rfl)
    rw [← hc']
    exact commutator_le_frattini hWp hc
  obtain ⟨k, hk⟩ := (CFSG.GroupTheory.frattini_automorphism_kernel hWp).2 ⟨βW, hβWker⟩
  have hk' : βW ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have hβW1 : βW = 1 := by
    have h1 : orderOf βW ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
    have h2 : orderOf βW ∣ orderOf β := orderOf_map_dvd _ β
    have h3 : orderOf βW ∣ Nat.gcd (orderOf β) (p ^ k) := Nat.dvd_gcd h2 h1
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k hβ), Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  have hfixW : ∀ w ∈ W, β w = w := by
    intro w hw
    have := congrArg (fun γ : MulAut ↥W => ((γ ⟨w, hw⟩ : ↥W) : T)) hβW1
    exact this
  have hCp : IsPGroup p ↥C := hT.to_subgroup C
  have hΦ : frattini ↥C ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hxZ := hCΦ (Subgroup.mem_map_of_mem C.subtype hx)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxZ.2 g g.2)
  set βC := MulAut.characteristic C β with hβC
  have hβCcop : (orderOf βC).Coprime p := Nat.Coprime.coprime_dvd_left (orderOf_map_dvd _ β) hβ
  have hβC1 : βC = 1 := CFSG.SectionRank.Ccomm.central_frattini_odd_aut_detection hp2 hCp hΦ βC
    hβCcop fun y hy => Subtype.ext (hfixW (y : T) (Subgroup.mem_map_of_mem C.subtype hy))
  have hfixC : ∀ c ∈ C, β c = c := fun c hc => by
    have := congrArg (fun γ : MulAut ↥C => ((γ ⟨c, hc⟩ : ↥C) : T)) hβC1
    exact this
  have hself : Subgroup.centralizer (C : Set T) ≤ C := by
    rw [hCcen]
    exact inf_le_left
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  have hcopT : (orderOf β).Coprime (Nat.card T) := by
    rw [hn]
    exact Nat.Coprime.pow_right n hβ
  exact CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_self_centralizing p hT C hself β
    (orderOf β) (pow_orderOf_eq_one β) hcopT hfixC

variable {X : Type} [Group X] [Finite X]

theorem isPElement_of_trivial_mod (hp2 : p ≠ 2) {P : Subgroup X} [P.Normal] (hP : IsPGroup p ↥P)
    (hcen : Subgroup.centralizer (P : Set X) ≤ P) {T : Type} [Group T] (e : T ≃* ↥P)
    {C : Subgroup T} (hC : IsThompsonCritical C) {y : X}
    (hy : ∀ w ∈ (omegaC p C).map (P.subtype.comp e.toMonoidHom),
      ⁅y, w⁆ ∈ ⁅(omegaC p C).map (P.subtype.comp e.toMonoidHom),
        (omegaC p C).map (P.subtype.comp e.toMonoidHom)⁆) :
    ∃ k : ℕ, y ^ (p ^ k) = 1 := by
  haveI : Finite T := Finite.of_equiv _ e.symm.toEquiv
  have hT : IsPGroup p T := hP.of_equiv e.symm
  set ψ : T →* X := P.subtype.comp e.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := P.subtype_injective.comp e.injective
  set WT := omegaC p C with hWT
  haveI := hC.1
  haveI : (CFSG.omega₁ (G := ↥C) (p := p)).Characteristic := CFSG.omega₁_characteristic _
  have hWTc : WT.Characteristic := inferInstance
  haveI : (⁅WT, WT⁆).Characteristic := inferInstance
  set α : MulAut T := (e.trans (MulAut.conjNormal y)).trans e.symm with hα
  have hψα1 : ∀ t : T, ψ (α t) = y * ψ t * y⁻¹ := by
    intro t
    simp [hψ, hα, MulAut.conjNormal_apply]
  have hψα : ∀ (n : ℕ) (t : T), ψ ((α ^ n) t) = y ^ n * ψ t * (y ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      rw [pow_succ, MulAut.mul_apply, ih, hψα1, pow_succ]
      group
  have hα1 : ∀ w ∈ WT, w⁻¹ * α w ∈ ⁅WT, WT⁆ := by
    intro w hw
    have h1 := hy (ψ w⁻¹) (Subgroup.mem_map_of_mem ψ (WT.inv_mem hw))
    rw [← Subgroup.map_commutator] at h1
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.1 h1
    have h2 : ψ (w⁻¹ * α w) = (ψ c)⁻¹ := by
      rw [hce, map_mul, map_inv, hψα1, commutatorElement_def]
      group
    have h3 : w⁻¹ * α w = c⁻¹ := hψinj (by rw [h2, map_inv])
    rw [h3]
    exact Subgroup.inv_mem _ hc
  have hαn : ∀ (n : ℕ), ∀ w ∈ WT, w⁻¹ * (α ^ n) w ∈ ⁅WT, WT⁆ := by
    intro n
    induction n with
    | zero => intro w _; simp
    | succ n ih =>
      intro w hw
      rw [pow_succ, MulAut.mul_apply]
      have h1 := hα1 w hw
      have e1 : α w = w * (w⁻¹ * α w) := by group
      rw [e1, map_mul]
      have h2 : (α ^ n) (w⁻¹ * α w) ∈ ⁅WT, WT⁆ :=
        CFSG.SectionRank.Ccomm.char_apply_mem inferInstance (α ^ n) h1
      have e2 : w⁻¹ * ((α ^ n) w * (α ^ n) (w⁻¹ * α w)) =
          (w⁻¹ * (α ^ n) w) * (α ^ n) (w⁻¹ * α w) := by group
      rw [e2]
      exact Subgroup.mul_mem _ (ih w hw) h2
  obtain ⟨a, b, hb, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos α).ne' p (Fact.out : p.Prime).ne_one
  have hβord : orderOf (α ^ (p ^ a)) = b := by
    rw [orderOf_pow_of_dvd (pow_ne_zero a (Fact.out : p.Prime).ne_zero) ⟨b, hord⟩, hord,
      Nat.mul_div_cancel_left _ (pow_pos (Fact.out : p.Prime).pos a)]
  have hβ1 : α ^ (p ^ a) = 1 := aut_eq_one_of_critical hp2 hT hC (α ^ (p ^ a))
    (by rw [hβord]; exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hb).symm) (hαn (p ^ a))
  have hyc : y ^ (p ^ a) ∈ Subgroup.centralizer (P : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨t, ht⟩ := e.surjective ⟨x, hx⟩
    have h1 := hψα (p ^ a) t
    rw [hβ1, MulAut.one_apply] at h1
    have hxt : ψ t = x := by rw [hψ]; simp [ht]
    rw [hxt] at h1
    calc x * y ^ p ^ a = (y ^ p ^ a * x * (y ^ p ^ a)⁻¹) * y ^ p ^ a := by rw [← h1]
      _ = y ^ p ^ a * x := by group
  obtain ⟨c, hc⟩ := hP ⟨_, hcen hyc⟩
  refine ⟨a + c, ?_⟩
  have := congrArg Subtype.val hc
  simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
  rw [pow_add, pow_mul, this]

theorem normal_omegaC_map {X : Type} [Group X] {P : Subgroup X} [P.Normal] {T : Type} [Group T]
    (e : T ≃* ↥P) {C : Subgroup T} (hC : IsThompsonCritical C) :
    ((omegaC p C).map (P.subtype.comp e.toMonoidHom)).Normal := by
  haveI := hC.1
  haveI : (CFSG.omega₁ (G := ↥C) (p := p)).Characteristic := CFSG.omega₁_characteristic _
  refine ⟨fun n hn y => ?_⟩
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hn
  set α : MulAut T := (e.trans (MulAut.conjNormal y)).trans e.symm with hα
  have h1 : (P.subtype.comp e.toMonoidHom) (α t) = y * (P.subtype.comp e.toMonoidHom) t * y⁻¹ := by
    simp [hα, MulAut.conjNormal_apply]
  rw [← h1]
  exact Subgroup.mem_map_of_mem _ (CFSG.SectionRank.Ccomm.char_apply_mem inferInstance α ht)

theorem pow_eq_one_of_mem_omegaC (hp2 : p ≠ 2) {T : Type} [Group T] [Finite T] (hT : IsPGroup p T)
    {C : Subgroup T} (hC : IsThompsonCritical C) {t : T} (ht : t ∈ omegaC p C) : t ^ p = 1 := by
  obtain ⟨-, hCΦ, -, -⟩ := hC
  have hΦ : frattini ↥C ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    have hxZ := hCΦ (Subgroup.mem_map_of_mem C.subtype hx)
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxZ.2 g g.2)
  obtain ⟨-, -, -, hset, -, -⟩ :=
    CFSG.SectionRank.Ccomm.central_frattini_odd_power_map hp2 (hT.to_subgroup C) hΦ
  obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 ht
  have hc' : c ^ p = 1 := by
    have : c ∈ ((CFSG.omega₁ (G := ↥C) (p := p) : Subgroup ↥C) : Set ↥C) := hc
    rw [hset] at this
    exact this
  rw [← map_pow, hc', map_one]

theorem commutator_omegaC_le_center {T : Type} [Group T] {C : Subgroup T} (hC : IsThompsonCritical C) :
    ⁅omegaC p C, omegaC p C⁆ ≤ centerOf (omegaC p C) := by
  obtain ⟨-, -, hcomm, -⟩ := hC
  have hWC : omegaC p C ≤ C := Subgroup.map_subtype_le _
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [mem_centerOf_iff']
  have hmem : ⁅a, b⁆ ∈ C ⊓ Subgroup.centralizer (C : Set T) :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (hWC hb))
  refine ⟨?_, fun w hw => Subgroup.mem_centralizer_iff.1 hmem.2 w (hWC hw)⟩
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb) (Subgroup.inv_mem _ ha))
    (Subgroup.inv_mem _ hb)

end Kernel

@[expose] def Input_GL3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (W : Subgroup Y), W.Normal → (∀ w ∈ W, w ^ 3 = 1) →
    Nat.card ↥W ≤ 3 ^ 3 * Nat.card ↥⁅W, W⁆ →
    (∀ y : Y, (∀ w ∈ W, ⁅y, w⁆ ∈ ⁅W, W⁆) → ∃ k : ℕ, y ^ (3 ^ k) = 1) →
    ¬ CFSG.HallHigman.IsPSolvable 3 Y →
    ∀ S : Sylow 3 Y, (⊤ : Subgroup Y) =
      ⨆ (Q : Subgroup Y) (_ : Q ≤ S ∧ Q.relIndex S = 3), Subgroup.normalizer (Q : Set Y)

section Rank4

open CFSG.SectionRank.Ccomm (IsThompsonCritical)

variable {X : Type} [Group X] [Finite X] {p : ℕ} {S Mb : Subgroup X}

theorem CoverData.four_le_pRank [Fact p.Prime] (hd : CoverData p X S Mb) {Q : Subgroup X}
    (hQS : Q ≤ S) (hQi : Q.relIndex S = p) : 4 ≤ CFSG.Open.pRank p Q := by
  obtain ⟨H, hHS, hHe, hHc⟩ := hd.rank5
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have h1 : Q.relIndex H ≤ p := by
    rw [← hQi]
    exact Subgroup.relIndex_le_of_le_right hHS (by rw [hQi]; omega)
  have h2 := Subgroup.relIndex_mul_card Q H
  rw [hHc] at h2
  have hQHe : IsElemAbelian p (Q ⊓ H) := hHe.mono inf_le_right
  obtain ⟨j, hj⟩ := hQHe.isPGroup.exists_card_eq
  have hj4 : 4 ≤ j := by
    by_contra hj4
    push Not at hj4
    have h3 : p ^ j ≤ p ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hj] at h2
    have h4 : p ^ 5 ≤ p * p ^ 3 := h2 ▸ Nat.mul_le_mul h1 h3
    have h5 : p * p ^ 3 < p ^ 5 := by
      have : p * p ^ 3 = p ^ 4 := by ring
      rw [this]
      exact Nat.pow_lt_pow_right hp1 (by norm_num)
    omega
  exact hj4.trans (le_pRank_of_card inf_le_left hQHe hj)

theorem CoverData.not_gen [Fact p.Prime] (hd : CoverData p X S Mb)
    (htop : (⊤ : Subgroup X) =
      ⨆ (Q : Subgroup X) (_ : Q ≤ (toSylow hd.syl : Subgroup X) ∧
        Q.relIndex (toSylow hd.syl : Subgroup X) = p), Subgroup.normalizer (Q : Set X)) : False := by
  apply hd.notTop
  rw [htop]
  exact iSup₂_le fun Q hQ => hd.gamma Q hQ.1 (hd.four_le_pRank hQ.1 hQ.2)

theorem rank4_core (hGL3 : Input_GL3) (hd : CoverData 3 X S Mb)
    (hcen : Subgroup.centralizer (CFSG.pCore 3 X : Set X) ≤ CFSG.pCore 3 X) {T : Type} [Group T]
    (e : T ≃* ↥(CFSG.pCore 3 X)) {C : Subgroup T} (hC : IsThompsonCritical C) :
    3 ^ 4 * Nat.card ↥⁅omegaC 3 C, omegaC 3 C⁆ ≤ Nat.card ↥(omegaC 3 C) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite T := Finite.of_equiv _ e.symm.toEquiv
  have hP3 : IsPGroup 3 ↥(CFSG.pCore 3 X) := CFSG.pCore_isPGroup
  have hT : IsPGroup 3 T := hP3.of_equiv e.symm
  by_contra hlt
  push Not at hlt
  set ψ : T →* X := (CFSG.pCore 3 X).subtype.comp e.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := (CFSG.pCore 3 X).subtype_injective.comp e.injective
  set WT := omegaC 3 C with hWT
  set W := WT.map ψ with hW
  have hcW : Nat.card ↥W = Nat.card ↥WT := Subgroup.card_map_of_injective hψinj
  have hcW' : Nat.card ↥⁅W, W⁆ = Nat.card ↥⁅WT, WT⁆ := by
    rw [hW, ← Subgroup.map_commutator, Subgroup.card_map_of_injective hψinj]
  have hle : Nat.card ↥W ≤ 3 ^ 3 * Nat.card ↥⁅W, W⁆ := by
    rw [hcW, hcW']
    have hdvd : Nat.card ↥⁅WT, WT⁆ ∣ Nat.card ↥WT :=
      Subgroup.card_dvd_of_le (Subgroup.commutator_le_self WT)
    obtain ⟨j, hj⟩ := hdvd
    obtain ⟨n, hn⟩ := (hT.to_subgroup WT).exists_card_eq
    have hjdvd : j ∣ 3 ^ n := hn ▸ Dvd.intro_left _ hj.symm
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hjdvd
    have hpos : 0 < Nat.card ↥⁅WT, WT⁆ := Nat.card_pos
    rw [hj, hi] at hlt ⊢
    have hi3 : i ≤ 3 := by
      by_contra hi3
      push Not at hi3
      have : 3 ^ 4 ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi3
      have : 3 ^ 4 * Nat.card ↥⁅WT, WT⁆ ≤ Nat.card ↥⁅WT, WT⁆ * 3 ^ i := by
        rw [mul_comm]; exact Nat.mul_le_mul_left _ this
      omega
    calc Nat.card ↥⁅WT, WT⁆ * 3 ^ i ≤ Nat.card ↥⁅WT, WT⁆ * 3 ^ 3 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num : 0 < 3) hi3)
      _ = 3 ^ 3 * Nat.card ↥⁅WT, WT⁆ := mul_comm _ _
  have hexp : ∀ w ∈ W, w ^ 3 = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, pow_eq_one_of_mem_omegaC (by norm_num) hT hC ht, map_one]
  have hker : ∀ y : X, (∀ w ∈ W, ⁅y, w⁆ ∈ ⁅W, W⁆) → ∃ k : ℕ, y ^ (3 ^ k) = 1 :=
    fun y hy => isPElement_of_trivial_mod (by norm_num) hP3 hcen e hC hy
  exact hd.not_gen (hGL3 X W (normal_omegaC_map e hC) hexp hle hker hd.not_isPSolvable _)

end Rank4


section Setting

open CFSG.SectionRank.Ccomm (IsThompsonCritical)

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

theorem setting_facts' (h : Cex127 G m p B M E A N D) (hA3 : CFSG.Open.pRank p A = 3)
    (hk : CFSG.Open.pRank p (E ⊓ A) = 2) {R₀ : Subgroup G} (hR₀ : IsSylowIn p M R₀) :
    IsSylowIn p ⊤ R₀ ∧ GLBCore p 4 R₀ ≤ M ∧
      ∀ H : Subgroup G, IsEkIn p 4 R₀ H → ∀ D : Subgroup G, D ≤ H → 2 ≤ CFSG.Open.pRank p D →
        Subgroup.normalizer (D : Set G) ≤ M := by
  have hF := h.toSec11.toSec10Fails
  have hEA := h.pair
  refine ⟨(lemma104_iv_holds hF hEA hk hR₀).2.2, (lemma104_v_holds hF hEA (Or.inr hA3) hR₀).2,
    fun H hH D hDH hD2 => ?_⟩
  obtain ⟨-, -, A', hA', hHA'⟩ := (lemma104_v_holds hF hEA (Or.inr hA3) hR₀).1 H hH
  have hcore : Subgroup.normalizer (D : Set G) ≤ GLBCore p 2 A' :=
    le_sSup ⟨D, hDH.trans hHA', hD2, rfl⟩
  exact hcore.trans hA'.2.clause_d

theorem exists_ekIn' [Fact p.Prime] {R : Subgroup G} (hR : IsSylowIn p ⊤ R) {Y : Subgroup G}
    {k : ℕ} (hY : k ≤ CFSG.Open.pRank p Y) : ∃ H : Subgroup G, IsEkIn p k R H := by
  obtain ⟨E₄, -, hE₄, hE₄c⟩ := exists_elemAbelian_card_pow_of_le_pRank' hY
  obtain ⟨x, -, T, hTp, -, hRT, hE₄T⟩ :=
    exists_conj_le_pGroup' (le_top : R ≤ ⊤) hR.2.1 (le_top : E₄ ≤ ⊤) hE₄.isPGroup
  have hTR : T = R := hR.2.2 T le_top hTp hRT
  rw [hTR] at hE₄T
  exact ⟨GLBConj x E₄, hE₄T, isElemAbelian_gLBConj x hE₄, by rw [card_gLBConj, hE₄c]⟩

theorem glaPPrimeCoreOf_le_of_hyperplanes' [Fact p.Prime] {X H M' : Subgroup G} (hHX : H ≤ X)
    (hH : IsElemAbelian p H) (hHc : Nat.card ↥H = p ^ 4)
    (hΓ : ∀ D : Subgroup G, D ≤ H → 2 ≤ CFSG.Open.pRank p D →
      Subgroup.normalizer (D : Set G) ≤ M') :
    GLAPPrimeCoreOf p X ≤ M' := by
  haveI : CFSG.IsElementaryAbelian p ↥H := hH.isElementaryAbelian
  haveI : Nontrivial ↥H := by
    rw [← Finite.one_lt_card_iff_nontrivial, hHc]
    exact Nat.one_lt_pow (by norm_num) (Fact.out : p.Prime).one_lt
  have hHV : H ≤ Subgroup.normalizer ((GLAPPrimeCoreOf p X : Subgroup G) : Set G) :=
    hHX.trans (le_normalizer_glaPPrimeCoreOf p X)
  have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers hHV
    (Claims1211.not_dvd_card_glaPPrimeCoreOf X)
  refine hgen.trans (iSup₂_le fun B hB => ?_)
  have hDH : B.map H.subtype ≤ H := Subgroup.map_subtype_le B
  have hBc : Nat.card ↥B = p ^ 3 := by
    have h1 := B.card_mul_index
    rw [hB, hHc] at h1
    have : Nat.card ↥B * p = p ^ 3 * p := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos this
  have hDc : Nat.card ↥(B.map H.subtype) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, hBc]
  have hrank : 2 ≤ CFSG.Open.pRank p (B.map H.subtype) :=
    le_trans (by norm_num) (le_pRank_of_card le_rfl (hH.mono hDH) hDc)
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans (hΓ _ hDH hrank))

theorem core_le' [Fact p.Prime] (h : Cex127 G m p B M E A N D) (hA3 : CFSG.Open.pRank p A = 3)
    (hk : CFSG.Open.pRank p (E ⊓ A) = 2) {Y : Subgroup G} (hY : 4 ≤ CFSG.Open.pRank p Y) {z : G}
    (hz1 : IsPCentralIn p M z) :
    GLAPPrimeCoreOf p (Cg z) ≤ M ∧ pPrimePCore p (Cg z) ≤ M := by
  obtain ⟨R₀, hR₀M, hzR₀⟩ := hz1
  obtain ⟨hR₀G, -, hΓ⟩ := setting_facts' h hA3 hk hR₀M
  have hR₀C : R₀ ≤ Cg z := le_cg_of_mem_centerOf hzR₀
  obtain ⟨H, hH⟩ := exists_ekIn' hR₀G hY
  have hO : GLAPPrimeCoreOf p (Cg z) ≤ M :=
    glaPPrimeCoreOf_le_of_hyperplanes' (hH.1.trans hR₀C) hH.2.1 hH.2.2 (hΓ H hH)
  have hR₀S : IsSylowIn p (Cg z) R₀ :=
    ⟨hR₀C, hR₀G.2.1, fun R' _ hR'p hle => hR₀G.2.2 R' le_top hR'p hle⟩
  exact ⟨hO, (pPrimePCore_le_sup hR₀S).trans (sup_le hO hR₀M.1)⟩

theorem sylow_of_pCentral (h : Cex127 G m p B M E A N D) (hA3 : CFSG.Open.pRank p A = 3)
    (hk : CFSG.Open.pRank p (E ⊓ A) = 2) {z : G} (hz1 : IsPCentralIn p M z) :
    ∃ R : Subgroup G, IsSylowIn p (Cg z) R ∧ R ≤ M ∧ z ∈ centerOf R := by
  obtain ⟨R₀, hR₀M, hzR₀⟩ := hz1
  obtain ⟨hR₀G, -, -⟩ := setting_facts' h hA3 hk hR₀M
  exact ⟨R₀, ⟨le_cg_of_mem_centerOf hzR₀, hR₀G.2.1, fun R' _ hR'p hle => hR₀G.2.2 R' le_top hR'p hle⟩,
    hR₀M.1, hzR₀⟩

theorem sylow_facts' [Fact p.Prime] (h : Cex127 G m p B M E A N D) (hA3 : CFSG.Open.pRank p A = 3)
    (hk : CFSG.Open.pRank p (E ⊓ A) = 2) {z : G} (hz1 : IsPCentralIn p M z) {R : Subgroup G}
    (hR : IsSylowIn p (Cg z) R) (hRM : R ≤ M) :
    IsSylowIn p ⊤ R ∧ GLBCore p 4 R ≤ M ∧
      ∀ H : Subgroup G, IsEkIn p 4 R H → ∀ D : Subgroup G, D ≤ H → 2 ≤ CFSG.Open.pRank p D →
        Subgroup.normalizer (D : Set G) ≤ M := by
  obtain ⟨R₀, hR₀M, hzR₀⟩ := hz1
  obtain ⟨hR₀G, -, -⟩ := setting_facts' h hA3 hk hR₀M
  have hR₀S : IsSylowIn p (Cg z) R₀ :=
    ⟨le_cg_of_mem_centerOf hzR₀, hR₀G.2.1, fun R' _ hR'p hle => hR₀G.2.2 R' le_top hR'p hle⟩
  obtain ⟨x, -, hx⟩ := exists_gLBConj_eq hR hR₀S
  have hRG : IsSylowIn p ⊤ R := hx ▸ isSylowIn_top_gLBConj hR₀G x
  have hRMs : IsSylowIn p M R := ⟨hRM, hR.2.1, fun R' _ hR'p hle => hRG.2.2 R' le_top hR'p hle⟩
  obtain ⟨-, h2, h3⟩ := setting_facts' h hA3 hk hRMs
  exact ⟨hRG, h2, h3⟩

theorem subgroupOf_inf_eq_bot [Fact p.Prime] {z : G} {R : Subgroup G} (hRp : IsPGroup p ↥R)
    (hRC : R ≤ Cg z) : R.subgroupOf (Cg z) ⊓ GLAPPrimeCore p ↥(Cg z) = ⊥ := by
  have hR'p : IsPGroup p ↥(R.subgroupOf (Cg z)) := isPGroup_subgroupOf hRC hRp
  have hOc : Nat.Coprime p (Nat.card ↥(GLAPPrimeCore p ↥(Cg z))) := CFSG.pPrimeCore_coprime_card
  obtain ⟨k, hk⟩ := hR'p.exists_card_eq
  apply disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard _)
  rw [hk]
  exact Nat.Coprime.pow_left k hOc

section PullbackP

variable {Y : Type} [Group Y] [Finite Y] {O : Subgroup Y} [O.Normal] {R' : Subgroup Y}

theorem isElemAbelian_pullback' (hRO : R' ⊓ O = ⊥) {Ū : Subgroup (Y ⧸ O)}
    (hŪ : IsElemAbelian p Ū) : IsElemAbelian p (Ū.comap (QuotientGroup.mk' O) ⊓ R') := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun u hu => ?_⟩
  · have hc := congrArg Subtype.val (hŪ.1.is_comm.comm ⟨_, a.2.1⟩ ⟨_, b.2.1⟩)
    simp only [Subgroup.coe_mul] at hc ⊢
    exact eq_of_mk_eq hRO (R'.mul_mem a.2.2 b.2.2) (R'.mul_mem b.2.2 a.2.2)
      (by rw [map_mul, map_mul]; exact hc)
  · have h3 := hŪ.2 _ hu.1
    exact eq_of_mk_eq hRO (R'.pow_mem hu.2 p) R'.one_mem (by rw [map_pow, h3, map_one])

theorem exists_elemAbelian_pullback' [Fact p.Prime] (hRO : R' ⊓ O = ⊥) {Ū : Subgroup (Y ⧸ O)}
    (hŪ : Ū ≤ R'.map (QuotientGroup.mk' O)) {k : ℕ} (hk : k ≤ CFSG.Open.pRank p Ū) :
    ∃ U : Subgroup Y, U ≤ Ū.comap (QuotientGroup.mk' O) ⊓ R' ∧ IsElemAbelian p U ∧
      Nat.card ↥U = p ^ k := by
  obtain ⟨Vb, hVU, hV, hVc⟩ := exists_elemAbelian_card_pow_of_le_pRank' hk
  refine ⟨Vb.comap (QuotientGroup.mk' O) ⊓ R', inf_le_inf_right _ (Subgroup.comap_mono hVU),
    isElemAbelian_pullback' hRO hV, ?_⟩
  rw [card_pullback hRO (hVU.trans hŪ), hVc]

end PullbackP

theorem exists_elemAbelian_image [Fact p.Prime] {z : G} {R : Subgroup G} (hR : IsSylowIn p (Cg z) R)
    (hRG : IsSylowIn p ⊤ R) {Y : Subgroup G} {k : ℕ} (hY : k ≤ CFSG.Open.pRank p Y) :
    ∃ H : Subgroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)),
      H ≤ (R.subgroupOf (Cg z)).map (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z))) ∧
        IsElemAbelian p H ∧ Nat.card ↥H = p ^ k := by
  have hRO := subgroupOf_inf_eq_bot hR.2.1 hR.1
  obtain ⟨H₅, hH₅R, hH₅, hH₅c⟩ := exists_ekIn' hRG hY
  have hUR : H₅.subgroupOf (Cg z) ≤ R.subgroupOf (Cg z) := Subgroup.subgroupOf_mono _ hH₅R
  refine ⟨(H₅.subgroupOf (Cg z)).map _, Subgroup.map_mono hUR, (hH₅.subgroupOf _).map _, ?_⟩
  rw [card_map_mk_of_le hRO hUR, ← hH₅c]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hH₅R.trans hR.1)).toEquiv

theorem coverData_of' [Fact p.Prime] (h : Cex127 G m p B M E A N D)
    (hA3 : CFSG.Open.pRank p A = 3) (hk : CFSG.Open.pRank p (E ⊓ A) = 2) {Y : Subgroup G}
    (hY : 5 ≤ CFSG.Open.pRank p Y) {z : G} (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M)
    {R : Subgroup G} (hR : IsSylowIn p (Cg z) R) (hRM : R ≤ M) :
    CoverData p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))
      ((R.subgroupOf (Cg z)).map (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z))))
      ((M.subgroupOf (Cg z)).map (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)))) := by
  obtain ⟨hRG, hΓ4, hΓ⟩ := sylow_facts' h hA3 hk hz1 hR hRM
  obtain ⟨hOM, -⟩ := core_le' h hA3 hk (le_trans (by norm_num) hY) hz1
  set O : Subgroup ↥(Cg z) := GLAPPrimeCore p ↥(Cg z) with hOdef
  set π : ↥(Cg z) →* ↥(Cg z) ⧸ O := QuotientGroup.mk' O with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  set R' : Subgroup ↥(Cg z) := R.subgroupOf (Cg z) with hR'def
  have hR'p : IsPGroup p ↥R' := isPGroup_subgroupOf hR.1 hR.2.1
  have hRO : R' ⊓ O = ⊥ := subgroupOf_inf_eq_bot hR.2.1 hR.1
  have hR'map : R'.map (Cg z).subtype = R := Subgroup.map_subgroupOf_eq_of_le hR.1
  have hOM' : O ≤ M.subgroupOf (Cg z) := fun o ho =>
    Subgroup.mem_subgroupOf.2 (hOM ⟨o, ho, rfl⟩)
  set P : Subgroup (↥(Cg z) ⧸ O) := R'.map π with hPdef
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowIn hR
  have hSR' : (S : Subgroup ↥(Cg z)) = R' := by
    rw [hR'def, ← hS]
    exact (Subgroup.comap_map_eq_self_of_injective (Cg z).subtype_injective _).symm
  have hPS : IsSylowIn p ⊤ P := by
    have := isSylowIn_top_of_sylow (S.mapSurjective hπs)
    rwa [Sylow.coe_mapSurjective, hSR'] at this
  set Mbar : Subgroup (↥(Cg z) ⧸ O) := (M.subgroupOf (Cg z)).map π with hMbar
  have KL : ∀ Qb : Subgroup (↥(Cg z) ⧸ O), Qb ≤ P →
      Subgroup.normalizer (((Qb.comap π ⊓ R').map (Cg z).subtype : Subgroup G) : Set G) ≤ M →
      Subgroup.normalizer (Qb : Set (↥(Cg z) ⧸ O)) ≤ Mbar := by
    intro Qb hQbP hN xb hxb
    obtain ⟨y, rfl⟩ := hπs xb
    have hQ₁p : IsPGroup p ↥(Qb.comap π ⊓ R') := hR'p.to_le inf_le_right
    have hW : Qb.comap π = CFSG.pPrimeCore p ↥(Cg z) ⊔ (Qb.comap π ⊓ R') := by
      apply le_antisymm
      · intro w hw
        obtain ⟨r, hr, hrw⟩ := hQbP hw
        have hrQ : r ∈ Qb.comap π ⊓ R' :=
          Subgroup.mem_inf.2 ⟨by rw [Subgroup.mem_comap, hrw]; exact hw, hr⟩
        have hro : r⁻¹ * w ∈ O := by
          rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hrw
          exact hrw
        have e : w = r * (r⁻¹ * w) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hrQ) (Subgroup.mem_sup_left hro)
      · refine sup_le (fun o ho => ?_) inf_le_left
        rw [Subgroup.mem_comap]
        have : π o = 1 := by
          rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact ho
        rw [this]
        exact Qb.one_mem
    have hyW : y ∈ Subgroup.normalizer
        ((CFSG.pPrimeCore p ↥(Cg z) ⊔ (Qb.comap π ⊓ R') : Subgroup ↥(Cg z)) : Set ↥(Cg z)) := by
      rw [← hW]
      exact Subgroup.le_normalizer_comap π hxb
    have hy := mem_normalizer_sup_of_normalizes hQ₁p hyW
    have hNQ : Subgroup.normalizer (((Qb.comap π ⊓ R') : Subgroup ↥(Cg z)) : Set ↥(Cg z)) ≤
        M.subgroupOf (Cg z) := by
      intro n hn
      rw [Subgroup.mem_subgroupOf]
      exact hN (Subgroup.le_normalizer_map (Cg z).subtype ⟨n, hn, rfl⟩)
    exact ⟨y, (sup_le hNQ hOM') hy, rfl⟩
  have hpbR : ∀ Qb : Subgroup (↥(Cg z) ⧸ O), (Qb.comap π ⊓ R').map (Cg z).subtype ≤ R :=
    fun Qb => (Subgroup.map_mono inf_le_right).trans hR'map.le
  have hpbRank : ∀ Qb : Subgroup (↥(Cg z) ⧸ O), Qb ≤ P → ∀ k : ℕ, k ≤ CFSG.Open.pRank p Qb →
      k ≤ CFSG.Open.pRank p ((Qb.comap π ⊓ R').map (Cg z).subtype) := by
    intro Qb hQbP k hk
    obtain ⟨U, hU, hUel, hUc⟩ := exists_elemAbelian_pullback' hRO hQbP hk
    refine le_pRank_of_card (Subgroup.map_mono hU) (hUel.map _) ?_
    rw [Subgroup.card_map_of_injective (Cg z).subtype_injective, hUc]
  refine ⟨hPS, Subgroup.map_mono (Subgroup.subgroupOf_mono _ hRM), fun Qb hQbP hrk => ?_,
    fun Eb hEb => ?_, exists_elemAbelian_image hR hRG hY, ?_⟩
  · refine KL Qb hQbP ?_
    have hN0 : Subgroup.normalizer
        (((Qb.comap π ⊓ R').map (Cg z).subtype : Subgroup G) : Set G) ≤ GLBCore p 4 R :=
      le_sSup ⟨_, hpbR Qb, hpbRank Qb hQbP 4 hrk, rfl⟩
    exact hN0.trans hΓ4
  · unfold GLBCore
    refine sSup_le ?_
    rintro _ ⟨Tb, hTbE, hrk, rfl⟩
    refine KL Tb (hTbE.trans hEb.1) ?_
    have hH : IsEkIn p 4 R ((Eb.comap π ⊓ R').map (Cg z).subtype) := by
      refine ⟨hpbR Eb, (isElemAbelian_pullback' hRO hEb.2.1).map _, ?_⟩
      rw [Subgroup.card_map_of_injective (Cg z).subtype_injective, card_pullback hRO hEb.1,
        hEb.2.2]
    exact hΓ _ hH _ (Subgroup.map_mono (inf_le_inf_right _ (Subgroup.comap_mono hTbE)))
      (hpbRank Tb (hTbE.trans hEb.1) 2 hrk)
  · intro htop
    apply hz2
    intro c hc
    obtain ⟨m', hm', hm'eq⟩ := htop (Subgroup.mem_top (π ⟨c, hc⟩))
    have hO' : m'⁻¹ * ⟨c, hc⟩ ∈ O := by
      rw [hπdef, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hm'eq
      exact hm'eq
    have hcM : (⟨c, hc⟩ : ↥(Cg z)) ∈ M.subgroupOf (Cg z) := by
      have e : (⟨c, hc⟩ : ↥(Cg z)) = m' * (m'⁻¹ * ⟨c, hc⟩) := by group
      rw [e]
      exact Subgroup.mul_mem _ hm' (hOM' hO')
    exact Subgroup.mem_subgroupOf.1 hcM

theorem pCore_facts' [Fact p.Prime] {z : G}
    (hcons : CFSG.ABGLocalTools.IsPConstrained p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)))
    {R : Subgroup G} (hR : IsSylowIn p (Cg z) R) :
    Subgroup.centralizer (CFSG.pCore p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)) :
        Set (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))) ≤
      CFSG.pCore p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)) ∧
    Nonempty (↥(R ⊓ pPrimePCore p (Cg z)) ≃*
      ↥(CFSG.pCore p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)))) := by
  set O : Subgroup ↥(Cg z) := GLAPPrimeCore p ↥(Cg z) with hOdef
  set X := ↥(Cg z) ⧸ O
  set π : ↥(Cg z) →* X := QuotientGroup.mk' O with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hbot : CFSG.pPrimeCore p X = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot (G := ↥(Cg z)) Fact.out
  have hOp : CFSG.Op_p'p p X = CFSG.pCore p X :=
    CFSG.Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (p := p) hbot
  refine ⟨?_, ?_⟩
  · have hsyl : CFSG.ABGLocalTools.IsSylowOf p (CFSG.pCore p X) (CFSG.Op_p'p p X) := by
      rw [← CFSG.ABGLocalTools.sup_eq_Op_p'p_iff_isSylowOf CFSG.pCore_isPGroup, hbot, bot_sup_eq,
        hOp]
    have := hcons _ hsyl
    rwa [hOp] at this
  · set R₁ := R ⊓ pPrimePCore p (Cg z) with hR₁
    have hR₁C : R₁ ≤ Cg z := inf_le_left.trans hR.1
    set R₁' : Subgroup ↥(Cg z) := R₁.subgroupOf (Cg z) with hR₁'
    have hRO : R₁' ⊓ O = ⊥ := subgroupOf_inf_eq_bot (isPGroup_of_le' hR.2.1 inf_le_left) hR₁C
    have hinj : Function.Injective (π.comp R₁'.subtype) := fun a b hab =>
      Subtype.ext (eq_of_mk_eq hRO a.2 b.2 hab)
    have hrange : (π.comp R₁'.subtype).range = CFSG.pCore p X := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
      apply le_antisymm
      · rintro _ ⟨r, hr, rfl⟩
        have hr2 : (r : G) ∈ pPrimePCore p (Cg z) := (Subgroup.mem_subgroupOf.1 hr).2
        obtain ⟨c, hc, hcr⟩ := Subgroup.mem_map.1 hr2
        have : c = r := Subtype.ext hcr
        rw [← this]
        exact hc
      · intro x hx
        obtain ⟨S, hS⟩ := exists_sylow_of_isSylowIn hR
        have hle := (CFSG.pCore_isPGroup (p := p) (G := X)).le_sylow_of_normal (S.mapSurjective hπs)
        have h1 := hle hx
        rw [Sylow.coe_mapSurjective] at h1
        obtain ⟨r, hr, rfl⟩ := h1
        have hrR : (r : G) ∈ R := by
          rw [← hS]
          exact ⟨r, hr, rfl⟩
        refine ⟨r, Subgroup.mem_subgroupOf.2 ⟨hrR, ⟨r, hx, rfl⟩⟩, rfl⟩
    exact ⟨(Subgroup.subgroupOfEquivOfLe hR₁C).symm.trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))⟩

theorem m3' [Fact p.Prime] (h : Cex127 G m p B M E A N D) (hA3 : CFSG.Open.pRank p A = 3)
    (hk : CFSG.Open.pRank p (E ⊓ A) = 2) {Y : Subgroup G} (hY : 4 ≤ CFSG.Open.pRank p Y) {z : G}
    (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M) {R : Subgroup G} (hR : IsSylowIn p (Cg z) R)
    (hRM : R ≤ M) (E' : Subgroup G) (hE'R : E' ≤ R ⊓ pPrimePCore p (Cg z))
    (hE' : IsElemAbelian p E') : Nat.card ↥E' ≤ p ^ 3 := by
  obtain ⟨-, hOM⟩ := core_le' h hA3 hk hY hz1
  obtain ⟨-, hΓ, -⟩ := sylow_facts' h hA3 hk hz1 hR hRM
  by_contra hgt
  push Not at hgt
  obtain ⟨j, hj⟩ := exists_card_eq_pow hE'.isPGroup
  have hj4 : 4 ≤ j := by
    by_contra hj4
    push Not at hj4
    have : p ^ j ≤ p ^ 3 := Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    omega
  have hrank : 4 ≤ CFSG.Open.pRank p (R ⊓ pPrimePCore p (Cg z)) :=
    hj4.trans (le_pRank_of_card hE'R hE' hj)
  have hN0 : Subgroup.normalizer ((R ⊓ pPrimePCore p (Cg z) : Subgroup G) : Set G) ≤
      GLBCore p 4 R :=
    le_sSup ⟨R ⊓ pPrimePCore p (Cg z), inf_le_left, hrank, rfl⟩
  have hOC : pPrimePCore p (Cg z) ≤ Cg z := Subgroup.map_subtype_le _
  have hCO : Cg z ≤ Subgroup.normalizer ((pPrimePCore p (Cg z) : Subgroup G) : Set G) := by
    have hn : ((pPrimePCore p (Cg z)).subgroupOf (Cg z)).Normal := by
      have e : (pPrimePCore p (Cg z)).subgroupOf (Cg z) =
          (CFSG.pCore p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))).comap
            (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z))) :=
        Subgroup.comap_map_eq_self_of_injective (Cg z).subtype_injective _
      rw [e]
      infer_instance
    exact Subgroup.le_normalizer_of_normal_subgroupOf hOC
  exact hz2 ((le_sup_normalizer_inf hR hOC hCO).trans (sup_le hOM (hN0.trans hΓ)))

theorem card_le_of_le_pCore' [Fact p.Prime] (h : Cex127 G m p B M E A N D)
    (hA3 : CFSG.Open.pRank p A = 3) (hk : CFSG.Open.pRank p (E ⊓ A) = 2) {Y : Subgroup G}
    (hY : 4 ≤ CFSG.Open.pRank p Y) {z : G} (hz1 : IsPCentralIn p M z) (hz2 : ¬ Cg z ≤ M)
    {R : Subgroup G} (hR : IsSylowIn p (Cg z) R) (hRM : R ≤ M)
    (e : ↥(R ⊓ pPrimePCore p (Cg z)) ≃* ↥(CFSG.pCore p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))))
    (U : Subgroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)))
    (hU : U ≤ CFSG.pCore p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))) (hUe : IsElemAbelian p U) :
    Nat.card ↥U ≤ p ^ 3 := by
  set P := CFSG.pCore p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))
  set R₁ := R ⊓ pPrimePCore p (Cg z)
  set U₂ : Subgroup ↥R₁ := (U.subgroupOf P).map e.symm.toMonoidHom
  have hc : Nat.card ↥(U₂.map R₁.subtype) = Nat.card ↥U := by
    rw [Subgroup.card_map_of_injective R₁.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv
  rw [← hc]
  exact m3' h hA3 hk hY hz1 hz2 hR hRM _ (Subgroup.map_subtype_le _)
    (((hUe.subgroupOf P).map _).map _)

theorem omegaOne_map_eq {R₁ : Subgroup G} (C : Subgroup ↥R₁) :
    omegaOne 3 (C.map R₁.subtype) = (omegaC 3 C).map R₁.subtype := by
  unfold omegaOne omegaC CFSG.omega₁ CFSG.omega
  rw [Subgroup.map_map, MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image, pow_one, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, hx3⟩
    refine ⟨⟨r, hr⟩, Subtype.ext (Subtype.ext (by simpa using hx3)), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, c.2, rfl⟩, ?_⟩
    have := congrArg (fun t : ↥C => ((t : ↥R₁) : G)) hc
    simpa using this

theorem card_omegaOne_map {R₁ : Subgroup G} (C : Subgroup ↥R₁) :
    Nat.card ↥(omegaOne 3 (C.map R₁.subtype)) = Nat.card ↥(omegaC 3 C) ∧
      Nat.card ↥⁅omegaOne 3 (C.map R₁.subtype), omegaOne 3 (C.map R₁.subtype)⁆ =
        Nat.card ↥⁅omegaC 3 C, omegaC 3 C⁆ := by
  rw [omegaOne_map_eq, ← Subgroup.map_commutator]
  exact ⟨Subgroup.card_map_of_injective R₁.subtype_injective,
    Subgroup.card_map_of_injective R₁.subtype_injective⟩

end Setting

theorem claim1211_rank4_of_inputs (hI : Input24_5) (hGL3 : Input_GL3) : Claim1211_rank4 := by
  intro G _ _ m p B M E A N D h K hK z hz hz1 hz2 R hR hAR hRM C hC
  have hcons := cTilde_isPConstrained hI h hK hz hz1 hz2
  obtain ⟨hcom, hp3, hE5, -⟩ := hK
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd := coverData_of' h hcom.2.1.1 hcom.2.1.2 hE5 hz1 hz2 hR hRM
  obtain ⟨hcen, ⟨e⟩⟩ := pCore_facts' hcons hR
  obtain ⟨h1, h2⟩ := card_omegaOne_map C
  rw [h1, h2]
  exact rank4_core hGL3 hd hcen e hC

@[expose] def Input30_14_Out : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (W : Subgroup Y), W.Normal → IsExtraspecialThreeFive W →
    (∀ y : Y, (∀ w ∈ W, ⁅y, w⁆ ∈ ⁅W, W⁆) → ∃ k : ℕ, y ^ (3 ^ k) = 1) →
    (∃ E : Subgroup Y, IsElemAbelian 3 E ∧ 9 * Nat.card ↥(E ⊓ CFSG.pCore 3 Y) ≤ Nat.card ↥E) →
    ¬ CFSG.HallHigman.IsPSolvable 3 Y →
    (∀ S : Sylow 3 Y, (⊤ : Subgroup Y) =
        ⨆ (Q : Subgroup Y) (_ : Q ≤ S ∧ Q.relIndex S = 3), Subgroup.normalizer (Q : Set Y)) ∨
      IsLpType 2 9 ↥(CFSG.GH74.GLS.oPrimeResidual 3 (Y ⧸ CFSG.pCore 3 Y)) ∨
        IsSL2Nine ↥(CFSG.GH74.GLS.oPrimeResidual 3 (Y ⧸ CFSG.pCore 3 Y))

section L29

open CFSG.SectionRank.Ccomm (IsThompsonCritical)

theorem map_centerOf_le {Γ Γ' : Type} [Group Γ] [Group Γ'] (f : Γ →* Γ') (H : Subgroup Γ) :
    (centerOf H).map f ≤ centerOf (H.map f) := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hxH, hxc⟩ := (mem_centerOf_iff' H x).1 hx
  rw [mem_centerOf_iff']
  refine ⟨Subgroup.mem_map_of_mem f hxH, ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  rw [← map_mul, ← map_mul, hxc h hh]

theorem oPrimeResidual_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    Nonempty (↥(CFSG.GH74.GLS.oPrimeResidual 3 A) ≃* ↥(CFSG.GH74.GLS.oPrimeResidual 3 B)) := by
  have h : (CFSG.GH74.GLS.oPrimeResidual 3 A).map e.toMonoidHom = CFSG.GH74.GLS.oPrimeResidual 3 B := by
    unfold CFSG.GH74.GLS.oPrimeResidual
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨a, ⟨k, hk⟩, rfl⟩
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    · rintro ⟨k, hk⟩
      refine ⟨e.symm x, ⟨k, ?_⟩, by simp⟩
      rw [← map_pow, hk, map_one]
  exact ⟨((CFSG.GH74.GLS.oPrimeResidual 3 A).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr h)⟩

theorem chat_equiv {G : Type} [Group G] [Finite G] (z : G) :
    Nonempty ((↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z)) ⧸ CFSG.pCore 3 (↥(Cg z) ⧸ GLAPPrimeCore 3 ↥(Cg z)) ≃*
      ↥(Cg z) ⧸ CFSG.GH74.GLS.pPrimePCore 3 ↥(Cg z)) := by
  set Y₀ := ↥(Cg z)
  set N₀ : Subgroup Y₀ := GLAPPrimeCore 3 Y₀
  set M₀ : Subgroup Y₀ := CFSG.GH74.GLS.pPrimePCore 3 Y₀
  have hNM : N₀ ≤ M₀ := by
    intro x hx
    show QuotientGroup.mk' (CFSG.pPrimeCore 3 Y₀) x ∈ CFSG.pCore 3 (Y₀ ⧸ CFSG.pPrimeCore 3 Y₀)
    have h1 : (x : Y₀ ⧸ CFSG.pPrimeCore 3 Y₀) = 1 := (QuotientGroup.eq_one_iff x).2 hx
    rw [QuotientGroup.mk'_apply, h1]
    exact Subgroup.one_mem _
  have hmap : M₀.map (QuotientGroup.mk' N₀) = CFSG.pCore 3 (Y₀ ⧸ N₀) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
    (QuotientGroup.quotientQuotientEquivQuotient N₀ M₀ hNM)⟩

theorem l29_core (hGL3 : Input_GL3) (hO : Input30_14_Out) {X : Type} [Group X] [Finite X]
    {S Mb : Subgroup X} (hd : CoverData 3 X S Mb)
    (hcen : Subgroup.centralizer (CFSG.pCore 3 X : Set X) ≤ CFSG.pCore 3 X)
    (hm3 : ∀ U : Subgroup X, U ≤ CFSG.pCore 3 X → IsElemAbelian 3 U → Nat.card ↥U ≤ 3 ^ 3) :
    IsLpType 2 9 ↥(CFSG.GH74.GLS.oPrimeResidual 3 (X ⧸ CFSG.pCore 3 X)) ∨
      IsSL2Nine ↥(CFSG.GH74.GLS.oPrimeResidual 3 (X ⧸ CFSG.pCore 3 X)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := CFSG.pCore 3 X with hPdef
  have hP3 : IsPGroup 3 ↥P := CFSG.pCore_isPGroup
  obtain ⟨⟨C, hC⟩, -⟩ := CFSG.SectionRank.Ccomm.thompson_critical_subgroup hP3
  set e : ↥P ≃* ↥P := MulEquiv.refl _ with he
  have h4 := rank4_core hGL3 hd hcen e hC
  set ψ : ↥P →* X := P.subtype.comp e.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := P.subtype_injective.comp e.injective
  set W := (omegaC 3 C).map ψ with hW
  have hWP : W ≤ P := by
    rintro _ ⟨t, -, rfl⟩
    exact (e t).2
  have hcW : Nat.card ↥W = Nat.card ↥(omegaC 3 C) := Subgroup.card_map_of_injective hψinj
  have hcW' : Nat.card ↥⁅W, W⁆ = Nat.card ↥⁅omegaC 3 C, omegaC 3 C⁆ := by
    rw [hW, ← Subgroup.map_commutator, Subgroup.card_map_of_injective hψinj]
  have hexp : ∀ w ∈ W, w ^ 3 = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, pow_eq_one_of_mem_omegaC (by norm_num) hP3 hC ht, map_one]
  have hcl : ⁅W, W⁆ ≤ centerOf W := by
    rw [hW, ← Subgroup.map_commutator]
    exact (Subgroup.map_mono (commutator_omegaC_le_center hC)).trans (map_centerOf_le ψ _)
  have hext : IsExtraspecialThreeFive W :=
    isExtraspecialThreeFive_of_card hexp hcl (fun U hUW hUe => hm3 U (hUW.trans hWP) hUe)
      (by rw [hcW, hcW']; exact h4)
  have hker : ∀ y : X, (∀ w ∈ W, ⁅y, w⁆ ∈ ⁅W, W⁆) → ∃ k : ℕ, y ^ (3 ^ k) = 1 :=
    fun y hy => isPElement_of_trivial_mod (by norm_num) hP3 hcen e hC hy
  have hE : ∃ E : Subgroup X, IsElemAbelian 3 E ∧ 9 * Nat.card ↥(E ⊓ P) ≤ Nat.card ↥E := by
    obtain ⟨H, -, hHe, hHc⟩ := hd.rank5
    refine ⟨H, hHe, ?_⟩
    have h1 := hm3 _ inf_le_right (hHe.mono inf_le_left)
    rw [hHc]
    calc 9 * Nat.card ↥(H ⊓ P) ≤ 9 * 3 ^ 3 := Nat.mul_le_mul_left _ h1
      _ = 3 ^ 5 := by norm_num
  rcases hO X W (normal_omegaC_map e hC) hext hker hE hd.not_isPSolvable with hgen | hL | hSL
  · exact (hd.not_gen (hgen _)).elim
  · exact Or.inl hL
  · exact Or.inr hSL

theorem claim1211_L29_of_inputs (hI : Input24_5) (hGL3 : Input_GL3) (hO : Input30_14_Out) :
    Claim1211_L29 := by
  intro G _ _ m p B M E A N D h K hK z hz hz1 hz2
  have hcons := cTilde_isPConstrained hI h hK hz hz1 hz2
  obtain ⟨hcom, hp3, hE5, -⟩ := hK
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨R, hR, hRM, -⟩ := sylow_of_pCentral h hcom.2.1.1 hcom.2.1.2 hz1
  have hd := coverData_of' h hcom.2.1.1 hcom.2.1.2 hE5 hz1 hz2 hR hRM
  obtain ⟨hcen, ⟨e⟩⟩ := pCore_facts' hcons hR
  have hm3 := card_le_of_le_pCore' h hcom.2.1.1 hcom.2.1.2 (le_trans (by norm_num) hE5) hz1 hz2 hR
    hRM e
  obtain ⟨f₁⟩ := chat_equiv z
  obtain ⟨f⟩ := oPrimeResidual_equiv f₁
  rcases l29_core hGL3 hO hd hcen hm3 with ⟨F, hF, hFin, hc, ⟨g⟩⟩ | ⟨F, hF, hFin, hc, ⟨g⟩⟩
  · exact Or.inl ⟨F, hF, hFin, hc, ⟨f.symm.trans g⟩⟩
  · exact Or.inr ⟨F, hF, hFin, hc, ⟨f.symm.trans g⟩⟩

end L29

@[expose] def Input1210b_wreathRk : Prop :=
  ∀ (G : Type) [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}
    (h : Cex127 G m p B M E A N D) {K : Subgroup G},
    Lemma129Common p M E A N K →
    ((∃ Q : ℕ, p ∣ Q - 1 ∧ IsLpType p Q (barOf p K)) ∨ (p = 5 ∧ IsSporType .Fi22 (barOf p K))) →
    Lemma129IvBData p N K E A →
    ∃ (F : Subgroup G) (a : G) (H : Subgroup G),
      IsEkIn p 2 A F ∧ a ∈ E ⊓ A ∧ A = F ⊔ Subgroup.zpowers a ∧
      CFSG.Open.IsElemAbelian p H ∧ F ≤ H ∧
      (∀ y ∈ E ⊓ A, ∀ x ∈ H, y * x * y⁻¹ ∈ H) ∧
      IsPGroup p ↥(H ⊔ (E ⊓ A)) ∧ ¬ H ≤ M ∧
      (∀ x ∈ A, x ∉ H → ∀ n ∈ H ⊔ (E ⊓ A), x * n = n * x → n ∈ A) ∧
      (∃ n ∈ H ⊔ (E ⊓ A), n ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧ n ∉ A) ∧
      a ∉ H ∧ Nat.card ↥H = p ^ (2 * p)

theorem input1210b_wreath_of_rk (hW : Input1210b_wreathRk) : Lemma1210.Input1210b_wreath := by
  intro G _ _ m p B M E A N D h K hK htype hdata
  obtain ⟨F, a, H, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, -⟩ := hW G h hK htype hdata
  exact ⟨F, a, H, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

@[expose] def Input_rankGL4 : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (Y : Type) [Group Y] [Finite Y] (W : Subgroup Y), W.Normal →
    (∀ w ∈ W, w ^ p = 1) → ⁅W, W⁆ ≤ centerOf W →
    (∀ U : Subgroup Y, U ≤ W → IsElemAbelian p U → Nat.card ↥U ≤ p ^ 3) →
    (∀ y : Y, (∀ w ∈ W, ⁅y, w⁆ ∈ ⁅W, W⁆) → ∃ k : ℕ, y ^ (p ^ k) = 1) →
    ∀ E : Subgroup Y, IsElemAbelian p E → Nat.card ↥E ≤ p ^ 4 * Nat.card ↥(E ⊓ CFSG.pCore p Y)

section NoBeta

theorem card_le_nine_of_l29 {Y : Type} [Group Y] (hY : IsLpType 2 9 Y ∨ IsSL2Nine Y)
    {P : Subgroup Y} (hP : IsPGroup 3 ↥P) : Nat.card ↥P ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : Nat.card Y ∣ 720 := by
    rcases hY with ⟨F, _, _, hF9, ⟨e⟩⟩ | ⟨F, _, _, hF9, ⟨e⟩⟩
    · have h1 : Nat.card ↥(StatedSL 2 F) = 720 := by
        rw [CFSG.Open.StatedAPI.card_statedSL_two, hF9]
        norm_num
      rw [Nat.card_congr e.toEquiv, ← h1]
      exact Subgroup.card_quotient_dvd_card _
    · rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF9]
      norm_num
  have hY0 : Nat.card Y ≠ 0 := fun h0 => by rw [h0] at hdvd; norm_num at hdvd
  haveI : Finite Y := Nat.finite_of_card_ne_zero hY0
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk2 : k ≤ 2 := by
    by_contra hk2
    push Not at hk2
    have h1 : 3 ^ 3 ∣ Nat.card ↥P := hk ▸ pow_dvd_pow 3 hk2
    have h2 := h1.trans ((Subgroup.card_subgroup_dvd_card P).trans hdvd)
    norm_num at h2
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem card_le_of_l29 {X : Type} [Group X] [Finite X]
    (hL : IsLpType 2 9 ↥(CFSG.GH74.GLS.oPrimeResidual 3 (X ⧸ CFSG.pCore 3 X)) ∨
      IsSL2Nine ↥(CFSG.GH74.GLS.oPrimeResidual 3 (X ⧸ CFSG.pCore 3 X)))
    (hm3 : ∀ U : Subgroup X, U ≤ CFSG.pCore 3 X → IsElemAbelian 3 U → Nat.card ↥U ≤ 3 ^ 3)
    {E : Subgroup X} (hE : IsElemAbelian 3 E) : Nat.card ↥E ≤ 3 ^ 5 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := CFSG.pCore 3 X with hPdef
  set π : X →* X ⧸ P := QuotientGroup.mk' P with hπ
  set Ob := CFSG.GH74.GLS.oPrimeResidual 3 (X ⧸ P) with hOb
  have hEO : E.map π ≤ Ob := by
    rintro _ ⟨x, hx, rfl⟩
    apply Subgroup.subset_closure
    exact ⟨1, by rw [pow_one, ← map_pow, hE.2 x hx, map_one]⟩
  have hEb : Nat.card ↥(E.map π) ≤ 9 := by
    have hp : IsPGroup 3 ↥((E.map π).subgroupOf Ob) := isPGroup_subgroupOf hEO (hE.isPGroup.map π)
    have := card_le_nine_of_l29 hL hp
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEO).toEquiv] at this
  have hcard : Nat.card ↥E = Nat.card ↥(E.map π) * Nat.card ↥(P ⊓ E) := by
    have h1 := Subgroup.relIndex_mul_card P E
    have hk : (π.comp E.subtype).ker = P.subgroupOf E := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.comp_apply, Subgroup.coe_subtype,
        hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have h2 : P.relIndex E = Nat.card ↥(E.map π) := by
      rw [Subgroup.relIndex, ← hk, Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1, h2]
  rw [hcard]
  have h3 := hm3 (P ⊓ E) inf_le_left (hE.mono inf_le_right)
  calc Nat.card ↥(E.map π) * Nat.card ↥(P ⊓ E) ≤ 9 * 3 ^ 3 := Nat.mul_le_mul hEb h3
    _ = 3 ^ 5 := by norm_num

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A N D : Subgroup G}

theorem zR_of_A0' [Fact p.Prime] (hp2 : p ≠ 2) (h : Cex127 G m p B M E A N D)
    (hA3 : CFSG.Open.pRank p A = 3) (hk : CFSG.Open.pRank p (E ⊓ A) = 2)
    (hx : ∃ x : G, (∃ k : ℕ, x ^ (p ^ k) = 1) ∧
      x ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧
      x ∉ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G))
    {z : G} (hz1 : IsPCentralIn p M z) {R : Subgroup G} (hR : IsSylowIn p (Cg z) R) :
    IsCyclic ↥(centerOf R) := by
  obtain ⟨x, ⟨kx, hxk⟩, hxN, hxC⟩ := hx
  have hF := h.toSec11.toSec10Fails
  have hEA := h.pair
  obtain ⟨R₀, hR₀M, hzR₀⟩ := hz1
  obtain ⟨hR₀G, -, -⟩ := setting_facts' h hA3 hk hR₀M
  have hR₀S : IsSylowIn p (Cg z) R₀ :=
    ⟨le_cg_of_mem_centerOf hzR₀, hR₀G.2.1, fun R' _ hR'p hle => hR₀G.2.2 R' le_top hR'p hle⟩
  obtain ⟨c, -, hc⟩ := exists_gLBConj_eq hR hR₀S
  have hRG : IsSylowIn p ⊤ R := hc ▸ isSylowIn_top_gLBConj hR₀G c
  have hEAp : IsPGroup p ↥(E ⊔ A) := lemma104_i_holds hF hEA
  obtain ⟨g, -, T, hTp, -, hRT, hEAT⟩ :=
    exists_conj_le_pGroup' (le_top : R ≤ ⊤) hRG.2.1 (le_top : E ⊔ A ≤ ⊤) hEAp
  have hTR : T = R := hRG.2.2 T le_top hTp hRT
  rw [hTR] at hEAT
  have hEARs : E ⊔ A ≤ GLBConj g⁻¹ R := by
    have := gLBConj_mono g⁻¹ hEAT
    rwa [gLBConj_inv_gLBConj] at this
  have hRsG : IsSylowIn p ⊤ (GLBConj g⁻¹ R) := isSylowIn_top_gLBConj hRG g⁻¹
  suffices hcyc : IsCyclic ↥(centerOf (GLBConj g⁻¹ R)) by
    have hmap : (GLBConj g⁻¹ R).map (MulAut.conj g⁻¹).toMonoidHom = R :=
      gLBConj_gLBConj_inv g R
    let e : ↥(GLBConj g⁻¹ R) ≃* ↥R :=
      ((GLBConj g⁻¹ R).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective).trans (MulEquiv.subgroupCongr hmap)
    exact isCyclic_centerOf_of_mulEquiv e hcyc
  by_contra hnc
  have hZp : IsPGroup p ↥(centerOf (GLBConj g⁻¹ R)) :=
    isPGroup_of_le' hRsG.2.1 (Subgroup.map_subtype_le _)
  haveI : Fact (IsPGroup p ↥(centerOf (GLBConj g⁻¹ R))) := ⟨hZp⟩
  obtain ⟨S₂, -, hS₂c, hS₂e⟩ := CFSG.lemma_4_5_a hp2 hnc
  set V : Subgroup G := S₂.map (centerOf (GLBConj g⁻¹ R)).subtype with hVdef
  have hVZ : V ≤ centerOf (GLBConj g⁻¹ R) := Subgroup.map_subtype_le _
  have hVel : IsElemAbelian p V :=
    (CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hS₂e).map _
  have hVc : Nat.card ↥V = p ^ 2 := by
    rw [hVdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hS₂c]
  have hVcomm : ∀ v ∈ V, ∀ r ∈ GLBConj g⁻¹ R, r * v = v * r := fun v hv r hr =>
    ((mem_centerOf_iff' (GLBConj g⁻¹ R) v).1 (hVZ hv)).2 r hr
  have hSC := lemma104_ii_holds hF hEA
  have hVle : ∀ X : Subgroup G, IsSCp p ⊤ X → X ≤ GLBConj g⁻¹ R → V ≤ X := by
    intro X hX hXR
    have hsup : IsElemAbelian p (V ⊔ X) := CFSG.Open.IsElemAbelian.sup_of_commute hVel hX.2.1
      (fun v hv e he => (hVcomm v hv e (hXR he)).symm)
    have := hX.2.2 (V ⊔ X) le_top hsup le_sup_right
    rw [← this]
    exact le_sup_left
  have hVE := hVle E hSC.1 (le_sup_left.trans hEARs)
  have hVA := hVle A hSC.2 (le_sup_right.trans hEARs)
  have hV0 : V = E ⊓ A := by
    have hA0el : IsElemAbelian p (E ⊓ A) := hSC.1.2.1.mono inf_le_left
    obtain ⟨j, hj⟩ := hA0el.isPGroup.exists_card_eq
    have hjle : j ≤ 2 := by
      have := le_pRank_of_card le_rfl hA0el hj
      rwa [hk] at this
    refine Subgroup.eq_of_le_of_card_ge (le_inf hVE hVA) ?_
    rw [hj, hVc]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hjle
  have hRsC : GLBConj g⁻¹ R ≤ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rw [← hV0] at ha
    exact (hVcomm a ha r hr).symm
  have hCN : Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) := Subgroup.centralizer_le_normalizer _
  have hRsN : IsSylowIn p (Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G)) (GLBConj g⁻¹ R) :=
    ⟨hRsC.trans hCN, hRsG.2.1, fun R' _ hR'p hle => hRsG.2.2 R' le_top hR'p hle⟩
  have hxp : IsPGroup p ↥(Subgroup.zpowers x) := by
    intro y
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 y.2
    refine ⟨kx, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxk, one_zpow]
  obtain ⟨n, hnN, S', hS'p, hS'N, hRsS', hxS'⟩ :=
    exists_conj_le_pGroup' hRsN.1 hRsN.2.1 (Subgroup.zpowers_le.2 hxN) hxp
  have hS'eq : S' = GLBConj g⁻¹ R := hRsN.2.2 S' hS'N hS'p hRsS'
  rw [hS'eq] at hxS'
  have hmem : n⁻¹ * x * n ∈ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := by
    apply hRsC
    apply hxS'
    rw [mem_gLBConj]
    have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
    rw [e]
    exact Subgroup.mem_zpowers x
  apply hxC
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have ha' : n⁻¹ * a * n⁻¹⁻¹ ∈ E ⊓ A :=
    (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hnN) a).1 ha
  rw [inv_inv] at ha'
  have hc' := (Subgroup.mem_centralizer_iff.1 hmem) _ ha'
  calc a * x = n * ((n⁻¹ * a * n) * (n⁻¹ * x * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * x * n) * (n⁻¹ * a * n)) * n⁻¹ := by rw [hc']
    _ = x * a := by group

theorem cTilde_isPConstrained' (hI : Input24_5) [Fact p.Prime] (h : Cex127 G m p B M E A N D)
    {z : G} (hz : z ∈ A ∧ z ≠ 1) {R : Subgroup G} (hR : IsSylowIn p (Cg z) R)
    {Mb : Subgroup (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))}
    (hd : CoverData p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z))
      ((R.subgroupOf (Cg z)).map (QuotientGroup.mk' (GLAPPrimeCore p ↥(Cg z)))) Mb)
    (hZR : IsCyclic ↥(centerOf R)) :
    CFSG.ABGLocalTools.IsPConstrained p (↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)) := by
  have hp2 : p ≠ 2 := h.standing.ne_two
  set O : Subgroup ↥(Cg z) := GLAPPrimeCore p ↥(Cg z) with hOdef
  set π : ↥(Cg z) →* ↥(Cg z) ⧸ O := QuotientGroup.mk' O with hπdef
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  set R' : Subgroup ↥(Cg z) := R.subgroupOf (Cg z) with hR'def
  have hRO : R' ⊓ O = ⊥ := subgroupOf_inf_eq_bot hR.2.1 hR.1
  have hOc : Nat.Coprime p (Nat.card ↥O) := CFSG.pPrimeCore_coprime_card
  have hCne : Cg z ≠ ⊤ := by
    intro htop
    have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Cg z := htop ▸ Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.1 hg
    rcases h.standing.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hbot | htop'
    · rw [hbot, Subgroup.mem_bot] at hzc
      exact hz.2 hzc
    · obtain ⟨a, b, hab⟩ := h.standing.nonabelian
      have hb : b ∈ Subgroup.center G := htop' ▸ Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  have hKX : CFSG.Open.IsKGroup (↥(Cg z) ⧸ O) :=
    CFSG.KCore.KGroupNonab.quotient CFSG.Open.isCatalogGroup_isoInvariant
      (CFSG.KCore.KProperNonab.kGroupNonab CFSG.Open.isCatalogGroup_isoInvariant
        h.standing.kProper (Cg z) hCne) O
  have hOX : GLAPPrimeCore p (↥(Cg z) ⧸ O) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot (G := ↥(Cg z)) Fact.out
  have hzC : z ∈ Cg z := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hZX : Subgroup.center (↥(Cg z) ⧸ O) ≠ ⊥ := by
    intro hbot
    have hmem : π ⟨z, hzC⟩ ∈ Subgroup.center (↥(Cg z) ⧸ O) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := hπs g
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.1 y.2
    rw [hbot, Subgroup.mem_bot, hπdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
    have hAel : IsElemAbelian p A := h.pair.1.2.1.1.1.2.1
    have hzp : orderOf z = p := orderOf_eq_prime (hAel.2 z hz.1) hz.2
    have hdvd := orderOf_dvd_natCard (⟨⟨z, hzC⟩, hmem⟩ : ↥O)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hzp] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hOc hdvd
  have h5 : 5 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥(Cg z) ⧸ O)) := by
    obtain ⟨H, -, hHe, hHc⟩ := hd.rank5
    exact le_pRank_of_card le_top hHe hHc
  have hPc : IsCyclic ↥(centerOf (R'.map π)) := by
    have hinj : Function.Injective (π.comp R'.subtype) := fun a b hab =>
      Subtype.ext (eq_of_mk_eq hRO a.2 b.2 hab)
    have hrange : (π.comp R'.subtype).range = R'.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    let e₂ : ↥R ≃* ↥(R'.map π) := (Subgroup.subgroupOfEquivOfLe hR.1).symm.trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))
    haveI := hZR
    let e : ↥(centerOf R) ≃* ↥(centerOf (R'.map π)) :=
      ((Subgroup.center ↥R).equivMapOfInjective R.subtype R.subtype_injective).symm.trans
        ((Subgroup.centerCongr e₂).trans
          ((Subgroup.center ↥(R'.map π)).equivMapOfInjective (R'.map π).subtype
            (R'.map π).subtype_injective))
    exact isCyclic_of_surjective e.toMonoidHom e.surjective
  rcases hI (↥(Cg z) ⧸ O) p hKX Fact.out hp2 hOX hZX h5 _ hd.syl hPc with hc | hgen
  · exact hc
  exfalso
  apply hd.notTop
  rw [hgen]
  refine sup_le ?_ (iSup₂_le fun Eb hEb => hd.gamma2 Eb hEb)
  unfold GLBCore
  refine sSup_le ?_
  rintro _ ⟨Q, hQ, hrk, rfl⟩
  exact hd.gamma Q hQ hrk

end NoBeta

theorem claim1211_noBeta_of_inputs (hW : Input1210b_wreathRk) (hI : Input24_5) (hGL3 : Input_GL3)
    (hO : Input30_14_Out) (hR4 : Input_rankGL4) : Claim1211_noBeta := by
  intro G _ _ m p B M E A N D h K hK htype hdata
  have hpp : p.Prime := h.standing.prime
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp2 : p ≠ 2 := h.standing.ne_two
  have hp3 : 3 ≤ p := by have := hpp.two_le; omega
  have hA3 : CFSG.Open.pRank p A = 3 := hK.2.1.1
  have hk : CFSG.Open.pRank p (E ⊓ A) = 2 := hK.2.1.2
  obtain ⟨F, a, H, -, haEA, -, hHe, -, -, hHp, -, hcentr, ⟨n, hnHA, hnN, hnA⟩, haH, hHc⟩ :=
    hW G h hK htype hdata
  have hHrk : 2 * p ≤ CFSG.Open.pRank p H := le_pRank_of_card le_rfl hHe hHc
  have hH5 : 5 ≤ CFSG.Open.pRank p H := le_trans (by omega) hHrk
  obtain ⟨z, hzA, hz1, hzc, hz2⟩ :=
    lemma1210_b_of_inputs (input1210b_wreath_of_rk hW) h hK ⟨htype, hdata⟩
  obtain ⟨R, hR, hRM, -⟩ := sylow_of_pCentral h hA3 hk hzc
  have hd := coverData_of' h hA3 hk hH5 hzc hz2 hR hRM
  have hx : ∃ x : G, (∃ k : ℕ, x ^ (p ^ k) = 1) ∧
      x ∈ Subgroup.normalizer ((E ⊓ A : Subgroup G) : Set G) ∧
      x ∉ Subgroup.centralizer ((E ⊓ A : Subgroup G) : Set G) := by
    obtain ⟨k, hk'⟩ := hHp ⟨n, hnHA⟩
    refine ⟨n, ⟨k, by simpa using congrArg Subtype.val hk'⟩, hnN, fun hnC => hnA ?_⟩
    exact hcentr a haEA.2 haH n hnHA ((Subgroup.mem_centralizer_iff.1 hnC) a haEA)
  have hZR := zR_of_A0' hp2 h hA3 hk hx hzc hR
  have hcons := cTilde_isPConstrained' hI h ⟨hzA, hz1⟩ hR hd hZR
  obtain ⟨hcen, ⟨e⟩⟩ := pCore_facts' hcons hR
  have hm3 := card_le_of_le_pCore' h hA3 hk (le_trans (by norm_num) hH5) hzc hz2 hR hRM e
  obtain ⟨hRG, -, -⟩ := sylow_facts' h hA3 hk hzc hR hRM
  obtain ⟨Eb, -, hEbe, hEbc⟩ := exists_elemAbelian_image hR hRG hHrk
  by_cases hp5 : 5 ≤ p
  · set X := ↥(Cg z) ⧸ GLAPPrimeCore p ↥(Cg z)
    set P := CFSG.pCore p X with hPdef
    have hP : IsPGroup p ↥P := CFSG.pCore_isPGroup
    obtain ⟨⟨C, hC⟩, -⟩ := CFSG.SectionRank.Ccomm.thompson_critical_subgroup hP
    set e' : ↥P ≃* ↥P := MulEquiv.refl _ with he'
    set ψ : ↥P →* X := P.subtype.comp e'.toMonoidHom with hψ
    set W := (omegaC p C).map ψ with hWdef
    have hWP : W ≤ P := by
      rintro _ ⟨t, -, rfl⟩
      exact (e' t).2
    have hexp : ∀ w ∈ W, w ^ p = 1 := by
      rintro _ ⟨t, ht, rfl⟩
      rw [← map_pow, pow_eq_one_of_mem_omegaC hp2 hP hC ht, map_one]
    have hcl : ⁅W, W⁆ ≤ centerOf W := by
      rw [hWdef, ← Subgroup.map_commutator]
      exact (Subgroup.map_mono (commutator_omegaC_le_center hC)).trans (map_centerOf_le ψ _)
    have hker : ∀ y : X, (∀ w ∈ W, ⁅y, w⁆ ∈ ⁅W, W⁆) → ∃ k : ℕ, y ^ (p ^ k) = 1 :=
      fun y hy => isPElement_of_trivial_mod hp2 hP hcen e' hC hy
    have hb := hR4 p hpp hp5 X W (normal_omegaC_map e' hC) hexp hcl
      (fun U hUW hUe => hm3 U (hUW.trans hWP) hUe) hker Eb hEbe
    have h3 := hm3 (Eb ⊓ P) inf_le_right (hEbe.mono inf_le_left)
    rw [hEbc] at hb
    have h7 : p ^ (2 * p) ≤ p ^ 7 := by
      calc p ^ (2 * p) ≤ p ^ 4 * Nat.card ↥(Eb ⊓ P) := hb
        _ ≤ p ^ 4 * p ^ 3 := Nat.mul_le_mul_left _ h3
        _ = p ^ 7 := by ring
    have h8 : p ^ 7 < p ^ (2 * p) := Nat.pow_lt_pow_right hpp.one_lt (by omega)
    omega
  · have hp3' : p = 3 := by
      interval_cases p
      · rfl
      · exact absurd hpp (by norm_num)
    subst hp3'
    have hb := card_le_of_l29 (l29_core hGL3 hO hd hcen hm3) hm3 hEbe
    rw [hEbc] at hb
    norm_num at hb

theorem lemma1211_of_inputs_b (h129 : Lemma129PrintedStatement) (hW : Input1210b_wreathRk)
    (hI : Input24_5) (hGL3 : Input_GL3) (hO : Input30_14_Out) (hR4 : Input_rankGL4) :
    Lemma1211Statement :=
  lemma1211_of_subclaims h129 lemma1210_holds (claim1211_rank4_of_inputs hI hGL3)
    (claim1211_L29_of_inputs hI hGL3 hO) (claim1211_noBeta_of_inputs hW hI hGL3 hO hR4)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1211b
