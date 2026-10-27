module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15OuterC
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15OuterA
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15OuterB

public section

namespace CFSG.QuasithinUnique.Unc25K1

open CFSG.Open CFSG.Quasithin

section Config

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs) {t zK : G}

theorem false_of_outer_stage2 (h : Lv2513 N t zK) (F : K33Facts N.K) (L : L33Facts N.K)
    (hKt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G)) {x' : G}
    (hx'P : x' ∈ T ⊓ Subgroup.normalizer (N.S : Set G)) (hx'S : x' ∉ N.S)
    (hx'c : ∀ v ∈ threeCoreCent N.K zK, x' * v = v * x') (hSC : N.SC = Subgroup.zpowers t) :
    False := by
  have hf := h.facts2511
  have hKH := H_le_normalizer_K N h F
  have hK0 := N.K0_eq hKH
  have hzKK := zK_mem_K N h F
  obtain ⟨hzz, -⟩ := z_eq_zK N h F hKt
  have htx : x'⁻¹ * t * x' = t * N.z := h.concl2513.1.2 x' hx'P hx'S
  have htx' : x'⁻¹ * t * x' = t * zK := by rw [htx, hzz]
  have hsimple : IsSimpleGroup ↥N.K := h.facts258.simple
  have hZK : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1 := fun x hx hc =>
    N.center_K_trivial hsimple hx hc
  have hz1 := zK_ne_one N hf
  have hz2 := zK_mul_self N hf
  have ht2 := t_mul_self N hf
  have htK : ∀ k ∈ N.K, k * t = t * k := fun k hk =>
    Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hf.t_mem) k (N.K_le_K0 hk)
  have hxz : x'⁻¹ * zK * x' = zK := by
    have h1 := Subgroup.mem_centralizer_iff.mp N.tuple.z_mem.2 x' hx'P.1
    rw [← hzz]
    calc x'⁻¹ * N.z * x' = x'⁻¹ * (N.z * x') := by group
      _ = x'⁻¹ * (x' * N.z) := by rw [h1]
      _ = N.z := by group
  obtain ⟨U, HU, E, hpair, hUS, hHU, hU, hESK, hE4, hzE⟩ := exists_pair_E N h F hKt
  have hzE' : zK ∈ E := hzz ▸ hzE
  obtain ⟨e, heE, he1, hez, he2, hecomm, hEgen⟩ := exists_e_of_four hE4 hzE' hz1
  have heS : e ∈ N.S := N.SK_le_S (hESK heE)
  have heK : e ∈ N.K := N.SK_le_K (hESK heE)
  have hEK : E ≤ N.K := hESK.trans N.SK_le_K
  have hy₁R0 : e⁻¹ * (x'⁻¹ * e * x') ∈ centSKz N.S N.K zK :=
    comm_mem_centSKz N h F hKt heS hx'P.2 hx'c
  obtain ⟨y₁, hy₁def⟩ : ∃ y₁ : G, y₁ = e⁻¹ * (x'⁻¹ * e * x') := ⟨_, rfl⟩
  rw [← hy₁def] at hy₁R0
  have hy₁R : y₁ ∈ centSKz N.S N.K zK := hy₁R0
  have hy₁S : y₁ ∈ N.S := (mem_centSKz_iff.mp hy₁R).1
  have hey : x'⁻¹ * e * x' = e * y₁ := by rw [hy₁def]; group
  have hy₁o : ¬ Ch1.InducesInner y₁ N.K := by
    intro hin
    obtain ⟨hy₁Z, -⟩ := R_inner_cls N h F hSC hy₁R hin
    have hy₁Q : y₁ ∈ Subgroup.zpowers t ⊔ E := by
      rw [hf.centerS_zK] at hy₁Z
      have hle : Subgroup.closure ({t, zK} : Set G) ≤ Subgroup.zpowers t ⊔ E := by
        rw [Subgroup.closure_le]
        intro w hw
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
        rcases hw with rfl | rfl
        · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
        · exact Subgroup.mem_sup_right hzE'
      exact hle hy₁Z
    refine false_of_normalizes N h F hpair hUS hHU hU hESK hzE hx'P hx'S htx ?_
    intro w hw
    rw [hEgen] at hw
    have key : ∀ w ∈ Subgroup.closure ({zK, e} : Set G),
        x'⁻¹ * w * x' ∈ Subgroup.zpowers t ⊔ E := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem v hv =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl
        · rw [hxz]
          exact Subgroup.mem_sup_right hzE'
        · rw [hey]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right heE) hy₁Q
      | one => simp
      | mul a b _ _ ha hb =>
        have : x'⁻¹ * (a * b) * x' = (x'⁻¹ * a * x') * (x'⁻¹ * b * x') := by group
        rw [this]
        exact Subgroup.mul_mem _ ha hb
      | inv a _ ha =>
        have : x'⁻¹ * a⁻¹ * x' = (x'⁻¹ * a * x')⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ ha
    exact key w hw
  have hy₁sq : y₁ * y₁ = zK := by
    rcases R_outer_cls N h F L hSC hy₁R hy₁o with h1 | h1
    · exact h1
    · exfalso
      have hy₂R : x'⁻¹ * y₁ * x' ∈ centSKz N.S N.K zK := conj_mem_centSKz hx'P.2 hx'c hy₁R
      have hy₂sq : (x'⁻¹ * y₁ * x') * (x'⁻¹ * y₁ * x') = t := by
        calc (x'⁻¹ * y₁ * x') * (x'⁻¹ * y₁ * x') = x'⁻¹ * (y₁ * y₁) * x' := by group
          _ = x'⁻¹ * (t * zK) * x' := by rw [h1]
          _ = (x'⁻¹ * t * x') * (x'⁻¹ * zK * x') := by group
          _ = (t * zK) * zK := by rw [htx', hxz]
          _ = t := by rw [mul_assoc, hz2, mul_one]
      by_cases hin₂ : Ch1.InducesInner (x'⁻¹ * y₁ * x') N.K
      · obtain ⟨-, hsq1⟩ := R_inner_cls N h F hSC hy₂R hin₂
        exact hf.t_ne_one (hy₂sq.symm.trans hsq1)
      · rcases R_outer_cls N h F L hSC hy₂R hin₂ with h2 | h2
        · rw [hy₂sq] at h2
          have htK' : t ∈ N.K := h2 ▸ hzKK
          exact hf.t_ne_one (hZK t htK' fun y hy => (htK y hy).symm)
        · rw [hy₂sq] at h2
          exact hz1 (by simpa using h2)
  have hy₁2K : y₁ * y₁ ∈ N.K := hy₁sq ▸ hzKK
  have hAut : IsAutPair N.K (N.K ⊔ Subgroup.zpowers y₁) :=
    isAutPair_of_outer N h F hy₁S hy₁o hy₁2K
  set A : Subgroup G := N.K ⊔ Subgroup.zpowers y₁ with hA
  have hAH : A ≤ N.H := sup_le N.K_le_H (Subgroup.zpowers_le.mpr (N.S_le_H hy₁S))
  have hAGt : A ≤ Subgroup.centralizer ({t} : Set G) := hAH.trans hf.H_le
  have hAt : ∀ a ∈ A, a * t = t * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hAGt ha)
  have htA : t ∉ A := by
    intro htA'
    have h1 : t ∈ A ⊓ Subgroup.centralizer (N.K : Set G) :=
      ⟨htA', Subgroup.mem_centralizer_iff.mpr fun k hk => htK k hk⟩
    rw [hAut.2.2, Subgroup.mem_bot] at h1
    exact hf.t_ne_one h1
  have hGt := Gt_decomp N h F L hKt hSC hy₁S hy₁o
  have hGt' : ∀ g : G, g * t = t * g → ∃ c ∈ Subgroup.zpowers t, ∃ a ∈ A, g = c * a :=
    fun g hg => hGt g (Subgroup.mem_centralizer_singleton_iff.mpr hg)
  obtain ⟨Fe, hFA, hFel, hFcard, hEF, hFK, hANF⟩ := L.e8_exists A hAut E hEK hE4
  have hQ := exists_elemAbelian_sup_zpowers Nat.prime_two hFel (n := 3)
    (by rw [hFcard]; norm_num) (c := t) hf.t_sq hf.t_ne_one
    (fun f hf' => hAt f (hFA hf')) (fun htF => htA (hFA htF))
  have hQ16 : Nat.card ↥(Fe ⊔ Subgroup.zpowers t) = 16 := by rw [hQ.2]; norm_num
  set Q : Subgroup G := Fe ⊔ Subgroup.zpowers t with hQdef
  have hFH : Fe ≤ N.H := hFA.trans hAH
  have hFE : Fe ≤ Subgroup.normalizer (E : Set G) := fun f hf' =>
    BenderBranch.mem_normalizer_of_forall_commute fun k hk =>
      isElemAbelian_mul_comm hFel hf' (hEF hk)
  have htH : t ∈ N.H := N.S_le_H (N.SC_le_S hf.t_mem)
  have htE : t ∈ Subgroup.normalizer (E : Set G) :=
    BenderBranch.mem_normalizer_of_forall_commute fun k hk => (htK k (hEK hk)).symm
  have hQHU : Q ≤ HU := by
    rw [hHU]
    exact sup_le (le_inf hFH hFE) (Subgroup.zpowers_le.mpr ⟨htH, htE⟩)
  have hHUQ : HU ≤ Subgroup.normalizer (Q : Set G) := by
    intro g hg
    rw [hHU] at hg
    obtain ⟨c, hc, a, ha, rfl⟩ := hGt g (hf.H_le hg.1)
    have hcE : c ∈ Subgroup.normalizer (E : Set G) := (Subgroup.zpowers_le.mpr htE) hc
    have haE : a ∈ Subgroup.normalizer (E : Set G) := by
      have h1 : c⁻¹ * (c * a) ∈ Subgroup.normalizer (E : Set G) :=
        (Subgroup.normalizer (E : Set G)).mul_mem
          ((Subgroup.normalizer (E : Set G)).inv_mem hcE) hg.2
      simpa using h1
    have haF : a ∈ Subgroup.normalizer (Fe : Set G) := hANF ⟨ha, haE⟩
    have haT : a ∈ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
      rw [normalizer_zpowers_eq_centralizer ht2]
      exact hAGt ha
    have haQ : a ∈ Subgroup.normalizer (Q : Set G) := mem_normalizer_sup haF haT
    have hcQ : c ∈ Subgroup.normalizer (Q : Set G) := by
      apply mem_normalizer_sup
      · refine BenderBranch.mem_normalizer_of_forall_commute fun f hf' => ?_
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
        exact (Commute.zpow_left (show Commute t f from (hAt f (hFA hf')).symm) m).eq
      · exact Subgroup.le_normalizer hc
    exact (Subgroup.normalizer (Q : Set G)).mul_mem hcQ haQ
  have hzQ : N.z ∈ Q := Subgroup.mem_sup_left (hEF hzE)
  have hQ2 : IsPGroup 2 ↥Q := isPGroup_two_of_sq fun x hx => hQ.1.2 x hx
  obtain ⟨-, hUsyl⟩ := ((h.concl2512 hKH).1 U HU hpair hUS).2 Q hQ2 hzQ hQHU hHUQ
  have he8' : ∀ F' : Subgroup G, F' ≤ A → CFSG.Assembly.IsElemAbelian 2 F' → Nat.card F' = 8 →
      ∃ a ∈ A, CFSG.conjugate Fe a = F' := fun F' hle hel hc =>
    L.e8_conj A hAut Fe F' hFA hle hFel hFcard hel hc
  have hWitt : ∀ g : G, g⁻¹ * t * g ∈ Q →
      ∃ n ∈ Subgroup.normalizer (Q : Set G), g⁻¹ * t * g = n⁻¹ * t * n := fun g hg =>
    witt_step htA ht2 hAt hGt' he8' hQ.1 hQ16 hg
  have hzK2 : zK ^ 2 = 1 := by rw [sq]; exact hz2
  have hEconj : ∀ f ∈ E, f ≠ 1 → ∃ k ∈ N.K, k⁻¹ * zK * k = f := fun f hfE hf1 =>
    L.inv_class zK hzKK f (hEK hfE) hz1 hf1 hzK2 (by rw [sq]; have := hE4.1.2 f hfE; rwa [sq] at this)
  have hFinv : ∀ f ∈ Fe, f * f = 1 := fun f hf' => by
    have := hFel.2 f hf'
    rwa [sq] at this
  have hey_involA : e * y₁ ∈ A :=
    A.mul_mem (Subgroup.mem_sup_left heK) (Subgroup.mem_sup_right (Subgroup.mem_zpowers y₁))
  have hey_notK : e * y₁ ∉ N.K := by
    intro hK'
    have : y₁ ∈ N.K := by
      have h1 : e⁻¹ * (e * y₁) ∈ N.K := N.K.mul_mem (N.K.inv_mem heK) hK'
      simpa using h1
    exact hy₁o (Ch1.InducesInner.of_mem this)
  have hey_sq : (e * y₁) * (e * y₁) = 1 := by
    rw [← hey]
    calc x'⁻¹ * e * x' * (x'⁻¹ * e * x') = x'⁻¹ * (e * e) * x' := by group
      _ = 1 := by rw [he2]; group
  have hT1 : ∀ f ∈ Fe, f ≠ 1 → ∃ g : G, g⁻¹ * N.z * g = f := by
    intro f hf' hf1
    by_cases hfK : f ∈ N.K
    · have hfE : f ∈ E := hFK ▸ (⟨hf', hfK⟩ : f ∈ Fe ⊓ N.K)
      obtain ⟨k, hk, hkf⟩ := hEconj f hfE hf1
      exact ⟨k, by rw [hzz]; exact hkf⟩
    · obtain ⟨a, haA, hconjf⟩ := L.outer_inv A hAut f (hFA hf') (e * y₁) hey_involA hfK hey_notK
        (by rw [sq]; exact hFinv f hf') (by rw [sq]; exact hey_sq)
      obtain ⟨k, hk, hke⟩ := hEconj e heE he1
      refine ⟨k * x' * a⁻¹, ?_⟩
      have hf_eq : f = a * (e * y₁) * a⁻¹ := by rw [← hconjf]; group
      rw [hzz, hf_eq, ← hey, ← hke]
      group
  have hT2E : ∀ f ∈ E, ∃ g : G, g⁻¹ * t * g = t * f := by
    intro f hfE
    by_cases hf1 : f = 1
    · exact ⟨1, by simp [hf1]⟩
    · obtain ⟨k, hk, hkf⟩ := hEconj f hfE hf1
      have hktk : k⁻¹ * t * k = t := by
        calc k⁻¹ * t * k = k⁻¹ * (t * k) := by group
          _ = k⁻¹ * (k * t) := by rw [← htK k hk]
          _ = t := by group
      refine ⟨x' * k, ?_⟩
      calc (x' * k)⁻¹ * t * (x' * k) = k⁻¹ * (x'⁻¹ * t * x') * k := by group
        _ = k⁻¹ * (t * zK) * k := by rw [htx']
        _ = (k⁻¹ * t * k) * (k⁻¹ * zK * k) := by group
        _ = t * f := by rw [hktk, hkf]
  have hT2 : ∀ f ∈ Fe, ∃ g : G, g⁻¹ * t * g = t * f := by
    intro f hf'
    by_cases hfK : f ∈ N.K
    · exact hT2E f (hFK ▸ (⟨hf', hfK⟩ : f ∈ Fe ⊓ N.K))
    · have hzA : zK ∈ A := Subgroup.mem_sup_left hzKK
      have hcomm : (e * y₁) * zK = zK * (e * y₁) :=
        comm_of_mem_center (zK_mem_center N hf) (N.S.mul_mem heS hy₁S)
      have hf₀A : (e * y₁) * zK ∈ A := A.mul_mem hey_involA hzA
      have hf₀K : (e * y₁) * zK ∉ N.K := by
        intro hK'
        apply hey_notK
        have h1 : (e * y₁) * zK * zK⁻¹ ∈ N.K := N.K.mul_mem hK' (N.K.inv_mem hzKK)
        simpa using h1
      have hf₀sq : ((e * y₁) * zK) * ((e * y₁) * zK) = 1 := by
        calc ((e * y₁) * zK) * ((e * y₁) * zK) = (e * y₁) * (zK * (e * y₁)) * zK := by group
          _ = (e * y₁) * ((e * y₁) * zK) * zK := by rw [← hcomm]
          _ = ((e * y₁) * (e * y₁)) * (zK * zK) := by group
          _ = 1 := by rw [hey_sq, hz2, one_mul]
      obtain ⟨a, haA, hconjf⟩ := L.outer_inv A hAut f (hFA hf') ((e * y₁) * zK) hf₀A hfK hf₀K
        (by rw [sq]; exact hFinv f hf') (by rw [sq]; exact hf₀sq)
      have htf₀ : x'⁻¹ * (t * e) * x' = t * ((e * y₁) * zK) := by
        calc x'⁻¹ * (t * e) * x' = (x'⁻¹ * t * x') * (x'⁻¹ * e * x') := by group
          _ = (t * zK) * (e * y₁) := by rw [htx', hey]
          _ = t * (zK * (e * y₁)) := by group
          _ = t * ((e * y₁) * zK) := by rw [← hcomm]
      obtain ⟨g₀, hg₀⟩ := hT2E e heE
      refine ⟨g₀ * x' * a⁻¹, ?_⟩
      have haf : a * ((e * y₁) * zK) * a⁻¹ = f := by rw [← hconjf]; group
      have hat : a * t = t * a := hAt a haA
      calc (g₀ * x' * a⁻¹)⁻¹ * t * (g₀ * x' * a⁻¹)
          = a * (x'⁻¹ * (g₀⁻¹ * t * g₀) * x') * a⁻¹ := by group
        _ = a * (x'⁻¹ * (t * e) * x') * a⁻¹ := by rw [hg₀]
        _ = a * (t * ((e * y₁) * zK)) * a⁻¹ := by rw [htf₀]
        _ = t * (a * ((e * y₁) * zK) * a⁻¹) := by
            calc a * (t * ((e * y₁) * zK)) * a⁻¹ = (a * t) * ((e * y₁) * zK) * a⁻¹ := by group
              _ = (t * a) * ((e * y₁) * zK) * a⁻¹ := by rw [hat]
              _ = t * (a * ((e * y₁) * zK) * a⁻¹) := by group
        _ = t * f := by rw [haf]
  have htQ : t ∈ Q := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hcommFt : ∀ x ∈ Fe, ∀ y ∈ Subgroup.zpowers t, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute x t from hAt x (hFA hx)) m).eq
  have hO' : ∀ o : G, (∃ n ∈ Subgroup.normalizer (Q : Set G), o = n * t * n⁻¹) ↔
      ∃ f ∈ Fe, o = t * f := by
    intro o
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hoQ : n * t * n⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hn t).mp htQ
      obtain ⟨f, hf', c, hc, hfc⟩ := mem_sup_of_commute hcommFt hoQ
      rcases mem_zpowers_involution ht2 hc with h1 | h1
      · exfalso
        rw [h1, mul_one] at hfc
        have hf1 : f ≠ 1 := by
          intro h0
          rw [h0] at hfc
          apply hf.t_ne_one
          calc t = n⁻¹ * (n * t * n⁻¹) * n := by group
            _ = 1 := by rw [← hfc]; group
        obtain ⟨g, hg⟩ := hT1 f hf' hf1
        apply hf.not_conj (g * n)
        calc (g * n)⁻¹ * N.z * (g * n) = n⁻¹ * (g⁻¹ * N.z * g) * n := by group
          _ = n⁻¹ * f * n := by rw [hg]
          _ = t := by rw [hfc]; group
      · refine ⟨f, hf', ?_⟩
        rw [h1] at hfc
        rw [← hfc]
        exact hAt f (hFA hf')
    · rintro ⟨f, hf', rfl⟩
      obtain ⟨g, hg⟩ := hT2 f hf'
      have hmem : g⁻¹ * t * g ∈ Q := by
        rw [hg]
        exact Subgroup.mul_mem _ htQ (Subgroup.mem_sup_left hf')
      obtain ⟨n, hn, hnt⟩ := hWitt g hmem
      refine ⟨n⁻¹, (Subgroup.normalizer (Q : Set G)).inv_mem hn, ?_⟩
      calc t * f = g⁻¹ * t * g := hg.symm
        _ = n⁻¹ * t * n := hnt
        _ = n⁻¹ * t * n⁻¹⁻¹ := by rw [inv_inv]
  have hcardO' :
      Nat.card {o : G // ∃ n ∈ Subgroup.normalizer (Q : Set G), o = n * t * n⁻¹} = 8 := by
    have hbij : Function.Bijective (fun f : Fe =>
        (⟨t * (f : G), (hO' _).mpr ⟨f, f.2, rfl⟩⟩ :
          {o : G // ∃ n ∈ Subgroup.normalizer (Q : Set G), o = n * t * n⁻¹})) := by
      constructor
      · intro f₁ f₂ h12
        have := congrArg Subtype.val h12
        exact Subtype.ext (mul_left_cancel this)
      · rintro ⟨o, ho⟩
        obtain ⟨f, hf', rfl⟩ := (hO' o).mp ho
        exact ⟨⟨f, hf'⟩, rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), hFcard]
  have hUt : ∀ u ∈ U, u * t = t * u := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mp (hf.H_le (N.S_le_H (hUS hu)))
  have hodd := odd_orbit_card (Subgroup.normalizer (Q : Set G)) t U hUt hUsyl.2.2
  rw [hcardO'] at hodd
  exact hodd (by norm_num)

end Config

end CFSG.QuasithinUnique.Unc25K1
