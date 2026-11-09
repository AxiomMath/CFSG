module

import CFSG.Certificates.Kernel.Common.Eval
meta import CFSG.Certificates.Kernel.BabyMonster.Twin
meta import CFSG.Certificates.Kernel.BabyMonster.TwinRank
import CFSG.Certificates.Kernel.BabyMonster.Five.Data18
import CFSG.Certificates.Kernel.BabyMonster.Five.Data19
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data2
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data8
import CFSG.Certificates.Kernel.BabyMonster.FiveA.Data23

#kc_eval CFSG.KC.BM.FiveA p157 CFSG.KC.BM.Twin.prod 4370 0 0 p154 v151
#kc_eval CFSG.KC.BM.FiveA p158 CFSG.KC.BM.Twin.prod 4370 0 0 p157 p157
#kc_eval CFSG.KC.BM.FiveA v160 CFSG.KC.BM.Twin.prod 4370 0 0 CFSG.KC.BM.Five.f85 CFSG.KC.BM.Five.Zp2
#kc_eval CFSG.KC.BM.FiveA v161 CFSG.KC.BM.Twin.prod 4370 0 0 p158 v147
#kc_eval CFSG.KC.BM.FiveA v162 CFSG.KC.BM.Twin.prod 4370 0 0 v159 v160 v161
#kc_eval CFSG.KC.BM.FiveA p163 CFSG.KC.BM.Twin.prod 4370 0 0 v162 v162
#kc_eval CFSG.KC.BM.FiveA p164 CFSG.KC.BM.Twin.prod 4370 0 0 p163 p163
#kc_eval CFSG.KC.BM.FiveA p165 CFSG.KC.BM.Twin.prod 4370 0 0 p163 v162
#kc_eval CFSG.KC.BM.FiveA v166 CFSG.KC.BM.Twin.prod 4370 0 0 v162 p55 p164
#kc_eval CFSG.KC.BM.FiveA v167 CFSG.KC.BM.Twin.prod 4370 0 0 p119 v166
#kc_eval CFSG.KC.BM.FiveA v168 CFSG.KC.BM.Twin.prod 4370 0 0 v162 v167 p164
#kc_eval CFSG.KC.BM.FiveA v169 CFSG.KC.BM.Twin.prod 4370 0 0 p165 v167 p163 v168
#kc_eval CFSG.KC.BM.FiveA v170 CFSG.KC.BM.Twin.prod 4370 0 0 p55 v169
#kc_eval CFSG.KC.BM.FiveA v171 CFSG.KC.BM.Twin.prod 4370 0 0 v162 v170 p164
#kc_eval CFSG.KC.BM.FiveA v172 CFSG.KC.BM.Twin.prod 4370 0 0 v170 v171
#kc_eval CFSG.KC.BM.FiveA v173 CFSG.KC.BM.Twin.prod 4370 0 0 v162 v172 p164
#kc_eval CFSG.KC.BM.FiveA v174 CFSG.KC.BM.Twin.prod 4370 0 0 p165 v172 p163 v173
#kc_eval CFSG.KC.BM.FiveA v175 CFSG.KC.BM.Twin.prod 4370 0 0 v170 v174
#kc_eval CFSG.KC.BM.FiveA v176 CFSG.KC.BM.Twin.prod 4370 0 0 v161 v175
#kc_eval CFSG.KC.BM.FiveA v179 CFSG.KC.BM.Twin.prod 4370 0 0 v176 v159
#kc_eval CFSG.KC.BM.FiveA c182 CFSG.KC.BM.Twin.prod 4370 0 0 v179 v160
#kc_eval CFSG.KC.BM.FiveA PrkW89 CFSG.KC.BM.Twin.rank 4370 0 0 v179 1 1
#kc_eval CFSG.KC.BM.FiveA RrkW89 CFSG.KC.BM.Twin.polyMul 4370 0 0 PrkW89 v179 1 1
